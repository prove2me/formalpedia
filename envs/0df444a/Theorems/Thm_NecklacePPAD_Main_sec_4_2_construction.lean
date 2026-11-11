-- Prove2me | Theorems.Thm_NecklacePPAD_Main_sec_4_2_construction
-- name    : NecklacePPAD.Main.sec_4_2_construction
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:10:02.908058+00:00
-- url     : https://prove2.me/theorems/5c92e2fd-f644-4ca4-84b7-1b62a1e1d766
-- title:
--   §4.2 construction properties — every colour occurs 2b_d times, the necklace is rigid, Σ^c_i are the sensor beads of segment i, polynomial time, n = |G_NOR| + 3|G_PURIFY|
-- statement:
--   Fix half-sizes $b_{\rm NOR}\ge5$, $b_{\rm NP}\ge4$, $b_{\rm NOT}\ge3$. For every Pure-Circuit instance $(V,G)$ and every choice of the colour order and of the orders inside the $\Sigma^c_i$: each colour $d$ has exactly $m_d$ beads in its own block and one bead for each entry of its input list, so it occurs exactly $m_d+s_d=2b_d$ times (in particular the word is a necklace); the necklace is rigid with blocks $B(d_r)$; every block starts and ends with a home bead; for $i\in[1,m_c-1]$ the beads of $\Sigma^c_i$ are exactly the beads lying in segment $i$ of $c$, and they are sensor beads; the orientations $\tau(d_r)=(r-1)\bmod 2$ agree with Lemma 4.2; and there are $n=|G_{\rm NOR}|+3|G_{\rm PURIFY}|$ colours. Moreover the construction takes polynomial time: some polynomial-time computable map sends the code of every Pure-Circuit instance to the code of its (canonically ordered) necklace.
--
--   Differences from the source:
--   - reading: standing assumptions of §4.2: half-sizes b_NOR ≥ 5, b_NP ≥ 4, b_NOT ≥ 3 fixed, (V, G) a Pure-Circuit instance → hypotheses 5 ≤ H.bNOR, 4 ≤ H.bNP, 3 ≤ H.bNOT and I.WellFormed; reason: the section fixes them once at its top; Definition 3.2 requires distinct gate nodes and one gate per output
--   - encoding: colour order d_1, …, d_n "arbitrarily" and the beads of Σ^c_i "in any order" → an arbitrary Layout (a permutation of the colours and, for every c and i, any permutation of the canonical Σ^c_i); reason: every choice of the page is a Layout and conversely
--   - encoding: auxiliary nodes v′, w′ of a PURIFY gate; V⁺ → V⁺ = Fin n ⊕ (gate index × Bool), v′ = inr (k, false), w′ = inr (k, true); auxiliary slots of NOR gates are hosted by no colour; reason: a node type for V⁺; unused slots are never read
--   - encoding: B(c) a set of consecutive positions → an interval [lo c, hi c] with lo c ≤ hi c < N; reason: B(c) holds more than b_c ≥ 0 beads of colour c, so it is nonempty, and a nonempty set of consecutive positions is such an interval
--   - encoding: "takes polynomial time" → ∃ f, CookPvsNP.PolyTimeComputable f ∧ f (I.code) = (canonLayout I H).necklace.code for every well-formed I; reason: an algorithm must fix the free orders; the canonical one takes colours in gate order
--   - encoding: |G_PURIFY| → the number of gates that are not NOR gates; reason: every gate is NOR or PURIFY
--   - encoding: "the beads in Σ^c_i are exactly the sensor beads lying in segment i of c" → a position lies in segment i of c iff it holds a slot of Σ^c_i, and every sensor slot of colour d is a sensor bead of d; reason: the same statement about positions of the word
-- source:
--   Zeng, Wang, Cao, Dai, Wang, Necklace Splitting with Ten Beads per Colour is PPAD-Hard (STOC 2027 submission, sha256 d5b5449c…41ac), §4.2, closing paragraph, p. 7 (PDF 9)

import Mathlib
import Definitions.Def_NecklacePPAD_Main_Construction
import Definitions.Def_NecklacePPAD_Main_NSCounts

set_option autoImplicit false

namespace NecklacePPAD.Main

open Blocks LpBallVI.Affine

/-- **§4.2, properties of the construction** (Zeng, Wang, Cao, Dai, Wang, STOC 2027 submission,
sha256 d5b5449c…, closing paragraph of §4.2, p. 7 (PDF 9)). Fix half-sizes `b_NOR ≥ 5`, `b_NP ≥ 4`,
`b_NOT ≥ 3`. For every Pure-Circuit instance `(V, G)` and every choice of the colour order and of the
orders inside the `Σ^c_i`: each colour `d` has exactly `m_d` beads in its own block, one bead for
each entry of its input list, and occurs exactly `2b_d` times; the necklace is rigid with blocks
`B(d_r)`; every block starts and ends with a home bead; the beads in `Σ^c_i` are exactly the sensor
beads lying in segment `i` of `c`; the orientations `(r − 1) mod 2` agree with Lemma 4.2; there are
`n = |G_NOR| + 3|G_PURIFY|` colours. The construction (canonical orders) takes polynomial time. -/
theorem sec_4_2_construction (H : HalfSizes) (hNOR : 5 ≤ H.bNOR) (hNP : 4 ≤ H.bNP)
    (hNOT : 3 ≤ H.bNOT) :
    (∀ I : PCInst, I.WellFormed → ∀ L : Layout I H,
      (∀ d, homeCount L.necklace L.blocks d = mOf I H d) ∧
      (∀ d, ∀ k : Fin (gad I d).inputs.length, L.slots.count (Slot.sensor d k.val) = 1) ∧
      (∀ d, L.necklace.beads.count d = 2 * bOf I H d) ∧
      L.necklace.IsNecklace ∧
      L.necklace.IsRigid L.blocks ∧
      (∀ c, L.necklace.beads[L.blocks.lo c]? = some c ∧
        L.necklace.beads[L.blocks.hi c]? = some c) ∧
      (∀ c i, 1 ≤ i → i + 1 ≤ mOf I H c → ∀ q,
        (InSegment L.necklace L.blocks c i q ↔ ∃ e ∈ L.sig c i, L.slots[q]? = some e)) ∧
      (∀ q d k, L.slots[q]? = some (Slot.sensor d k) → IsSensor L.necklace L.blocks d q) ∧
      (∀ c, L.blocks.tau c = tauOrd L.ord c) ∧
      L.necklace.n = (I.gates.filter PCGate.isNor).length +
        3 * (I.gates.filter (fun g => !PCGate.isNor g)).length) ∧
    ∃ f : List Bool → List Bool, CookPvsNP.PolyTimeComputable f ∧
      ∀ I : PCInst, I.WellFormed → f I.code = (canonLayout I H).necklace.code := by sorry

end NecklacePPAD.Main
