-- Prove2me | Theorems.Thm_KawasakiSOS_Threshold_stage_admissibility
-- name    : KawasakiSOS.Threshold.stage_admissibility
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:04:48.326074+00:00
-- url     : https://prove2.me/theorems/fe4a2b3b-e30d-48c1-b642-6f258f0e021d
-- title:
--   Lemma 4.6: admissibility
-- statement:
--   Let $k\ge6$, let $x\ne y$ in $\Omega$, and let $S$ be a stage. Then $S$ is admissible, that is, $r_z,r_w\ge0$, if one of the following holds:
--
--   1. $U=\emptyset$;
--   2. $T=\emptyset$;
--   3. $s_a\in W_A$ and $s_b\in W_B$ for an admissible pair $(s_a,s_b)$.
--
--   This is where the climbers are used: their equal heights keep both reservoirs nonnegative.
--
--   Differences from the source:
--   - reading: "s_a ∈ W_A and s_b ∈ W_B for an admissible pair" → the lifted sites p0 + s_a and p0 + s_b lie in the windows, with s_a ≤ s_b; reason: the page uses lifted coordinates and site pairs of climbers with a ≤ m ≤ b; its proof reads "W_A precedes U, which precedes W_B"
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), Lemma 4.6, p. 11 (PDF p. 12)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_Stage
import Definitions.Def_KawasakiSOS_Threshold_IsStage
import Definitions.Def_KawasakiSOS_Threshold_windowA
import Definitions.Def_KawasakiSOS_Threshold_arcU
import Definitions.Def_KawasakiSOS_Threshold_arcT
import Definitions.Def_KawasakiSOS_Threshold_cycleBase
import Definitions.Def_KawasakiSOS_Threshold_IsAdmissiblePair
import Definitions.Def_KawasakiSOS_Threshold_IsAdmissibleStage

namespace KawasakiSOS.Threshold

/-- Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), Lemma 4.6, p. 11 (PDF p. 12).

Formalization Notes:
- reading: "s_a ∈ W_A and s_b ∈ W_B for an admissible pair" → the lifted sites p0 + s_a and p0 + s_b lie in the windows, with s_a ≤ s_b. The page uses lifted coordinates and site pairs of climbers with a ≤ m ≤ b; its proof reads "W_A precedes U, which precedes W_B". -/
theorem stage_admissibility {n k : ℕ} [NeZero k] (hk : 6 ≤ k) (hkn : k ≤ n) (x y : Config n k) (hxy : x ≠ y) (S : Stage k) (hS : IsStage S)
    (h : arcU S = ∅ ∨ arcT S = ∅ ∨
      ∃ sa sb : ℕ, IsAdmissiblePair x y (cycleBase x y) sa sb ∧
        cycleBase x y + (sa : ZMod k) ∈ windowA S.cA ∧ cycleBase x y + (sb : ZMod k) = S.cB) :
    IsAdmissibleStage x y S := by sorry

end KawasakiSOS.Threshold
