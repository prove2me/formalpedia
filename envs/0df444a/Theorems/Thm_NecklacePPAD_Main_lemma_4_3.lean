-- Prove2me | Theorems.Thm_NecklacePPAD_Main_lemma_4_3
-- name    : NecklacePPAD.Main.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:07:08.051948+00:00
-- url     : https://prove2.me/theorems/4b5245f2-a88a-4195-8477-a47736a67c12
-- title:
--   Lemma 4.3 (gadget equation) — j(c) = b_c − s_c + S_c if τ(c) = 0 and j(c) = b_c − S_c if τ(c) = 1
-- statement:
--   In the situation of Lemma 4.2, suppose $B(c)$ starts and ends with a home bead. Let $m_c$ be the number of home beads of $c$ (then $m_c\ge b_c+1$), let $j(c)$ be the number of home beads of $c$ to the left of the unique cut inside $B(c)$ (then $j(c)\in[1,m_c-1]$), let $s_c$ be the number of sensor beads of $c$ and $S_c$ the number of sensor beads of $c$ with label 1. Then $j(c)=b_c-s_c+S_c$ if $\tau(c)=0$ and $j(c)=b_c-S_c$ if $\tau(c)=1$ (identities in $\mathbb Z$).
--
--   Differences from the source:
--   - encoding: 1-based positions [N], labels in {0,1}, ℓ(1) = 0 → 0-based positions, labels Bool (true = 1), lab ℓ 0 = false; reason: Lean indexing; the same labellings
--   - encoding: B(c) a set of consecutive positions → an interval [lo c, hi c] with lo c ≤ hi c < N; reason: B(c) holds more than b_c ≥ 0 beads of colour c, so it is nonempty, and a nonempty set of consecutive positions is such an interval
--   - encoding: a set C of n colours; balanced: exactly b_c of the 2b_c positions of colour c have label 1 → colours Fin n; 2·#{q : a_q = c, ℓ q} = count c; reason: same necklaces; the count of colour c is 2b_c
--   - reading: "(m_c ≥ b_c + 1)" and "let j(c) ∈ [1, m_c − 1] be …" stated in passing → both stated as conclusions; reason: the page asserts them as facts of the situation; the Lean states them explicitly
--   - encoding: j(c): home beads of c to the left of the unique cut inside B(c); s_c = 2b_c − m_c the number of sensor beads → jCut: home beads at positions ≤ some cut inside B(c); sensorCount: the number of sensor beads; reason: in the situation of Lemma 4.2 the cut inside B(c) is unique, and 2b_c − m_c is the number of sensor beads
--   - encoding: j(c) = b_c − s_c + S_c and j(c) = b_c − S_c → equalities of integers (casts to ℤ); reason: no truncated natural subtraction
-- source:
--   Zeng, Wang, Cao, Dai, Wang, Necklace Splitting with Ten Beads per Colour is PPAD-Hard (STOC 2027 submission, sha256 d5b5449c…41ac), Lemma 4.3, p. 6 (PDF 8)

import Mathlib
import Definitions.Def_NecklacePPAD_Main_Rigid

set_option autoImplicit false

namespace NecklacePPAD.Main

open Blocks

/-- **Lemma 4.3 (gadget equation)** (Zeng, Wang, Cao, Dai, Wang, STOC 2027 submission,
sha256 d5b5449c…, p. 6 (PDF 8)). In the situation of Lemma 4.2, suppose `B(c)` starts and ends with
a home bead. Then `m_c ≥ b_c + 1`, the number `j(c)` of home beads of `c` to the left of the unique
cut inside `B(c)` lies in `[1, m_c − 1]`, and with `s_c` the number of sensor beads of `c` and `S_c`
the number of sensor beads of `c` with label 1:
`j(c) = b_c − s_c + S_c` if `τ(c) = 0`, and `j(c) = b_c − S_c` if `τ(c) = 1`. -/
theorem lemma_4_3 (a : Necklace) (B : Blocks a.n) (ha : a.IsNecklace) (hB : a.IsRigid B)
    (ℓ : Fin a.N → Bool) (hℓ : a.IsSplit ℓ) (h0 : a.lab ℓ 0 = false) (c : Fin a.n)
    (hlo : a.beads[B.lo c]? = some c) (hhi : a.beads[B.hi c]? = some c) :
    a.half c + 1 ≤ homeCount a B c ∧
    1 ≤ jCut a B ℓ c ∧ jCut a B ℓ c + 1 ≤ homeCount a B c ∧
    (B.tau c = 0 →
      (jCut a B ℓ c : ℤ) = a.half c - sensorCount a B c + sensorOnes a B ℓ c) ∧
    (B.tau c = 1 → (jCut a B ℓ c : ℤ) = a.half c - sensorOnes a B ℓ c) := by sorry

end NecklacePPAD.Main
