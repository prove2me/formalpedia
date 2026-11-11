-- Prove2me | Theorems.Thm_NecklacePPAD_Main_lemma_4_6
-- name    : NecklacePPAD.Main.lemma_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:09:56.36464+00:00
-- url     : https://prove2.me/theorems/033daf21-d481-4c50-af28-3e62b8a008c5
-- title:
--   Lemma 4.6 — the sensor bead for an input y carries val(y) when val(y) ∈ {0, 1}
-- statement:
--   Under the standing assumptions of §4.2 (half-sizes $b_{\rm NOR}\ge5$, $b_{\rm NP}\ge4$, $b_{\rm NOT}\ge3$, a Pure-Circuit instance, any choice of orders), let $\ell$ be any split of the constructed necklace, complemented if necessary so that $\ell(1)=0$. Let $d$ be a gadget colour and $y$ an entry (the $k$-th) of its input list. If $\mathrm{val}(y)\in\{0,1\}$, the sensor bead of $d$ corresponding to $y$ has label $\mathrm{val}(y)$.
--
--   Differences from the source:
--   - reading: standing assumptions of §4.2: half-sizes b_NOR ≥ 5, b_NP ≥ 4, b_NOT ≥ 3 fixed, (V, G) a Pure-Circuit instance → hypotheses 5 ≤ H.bNOR, 4 ≤ H.bNP, 3 ≤ H.bNOT and I.WellFormed; reason: the section fixes them once at its top; Definition 3.2 requires distinct gate nodes and one gate per output
--   - encoding: colour order d_1, …, d_n "arbitrarily" and the beads of Σ^c_i "in any order" → an arbitrary Layout (a permutation of the colours and, for every c and i, any permutation of the canonical Σ^c_i); reason: every choice of the page is a Layout and conversely
--   - encoding: auxiliary nodes v′, w′ of a PURIFY gate; V⁺ → V⁺ = Fin n ⊕ (gate index × Bool), v′ = inr (k, false), w′ = inr (k, true); auxiliary slots of NOR gates are hosted by no colour; reason: a node type for V⁺; unused slots are never read
--   - encoding: ℓ any split, complemented if necessary so that ℓ(1) = 0; val(x) = R_{h(x)}(σ(x)) → Layout.normLab complements ℓ when lab ℓ 0 = true; Layout.val reads R with that labelling; reason: the page’s normalisation, made explicit
--   - encoding: the sensor bead of d corresponding to the entry y → the bead at sensorPos d k, the slot of the k-th entry of d’s input list; reason: the construction places one bead per entry
-- source:
--   Zeng, Wang, Cao, Dai, Wang, Necklace Splitting with Ten Beads per Colour is PPAD-Hard (STOC 2027 submission, sha256 d5b5449c…41ac), Lemma 4.6, p. 7 (PDF 9)

import Mathlib
import Definitions.Def_NecklacePPAD_Main_Construction

set_option autoImplicit false

namespace NecklacePPAD.Main

open LpBallVI.Affine

/-- **Lemma 4.6** (Zeng, Wang, Cao, Dai, Wang, STOC 2027 submission, sha256 d5b5449c…, p. 7
(PDF 9)). With half-sizes `b_NOR ≥ 5`, `b_NP ≥ 4`, `b_NOT ≥ 3`, a Pure-Circuit instance, any choice
of orders, and any split `ℓ` of the constructed necklace (normalised so that `ℓ(1) = 0`): for a
gadget colour `d` and the `k`-th entry `y` of its input list, the sensor bead of `d` corresponding
to `y` has label `val(y)` if `val(y) ∈ {0, 1}`. -/
theorem lemma_4_6 (H : HalfSizes) (hNOR : 5 ≤ H.bNOR) (hNP : 4 ≤ H.bNP) (hNOT : 3 ≤ H.bNOT)
    (I : PCInst) (hI : I.WellFormed) (L : Layout I H) (ℓ : Fin L.necklace.N → Bool)
    (hℓ : L.necklace.IsSplit ℓ) (d : Fin (numColours I)) (k : Fin (gad I d).inputs.length)
    (hy : L.val ℓ ((gad I d).inputs.get k) ≠ .bot) :
    PVal.ofBool (L.necklace.lab (L.normLab ℓ) (L.sensorPos d k.val)) =
      L.val ℓ ((gad I d).inputs.get k) := by sorry

end NecklacePPAD.Main
