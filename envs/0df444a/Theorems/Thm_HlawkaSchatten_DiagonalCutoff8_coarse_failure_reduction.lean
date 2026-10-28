-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_coarse_failure_reduction
-- name    : HlawkaSchatten.DiagonalCutoff8.coarse_failure_reduction
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T15:25:12.67891+00:00
-- url     : https://prove2.me/theorems/f3df31c7-6adc-47d0-b138-fd32fccfeac9
-- title:
--   Relative-coordinate reduction of a Hlawka counterexample for p >= 8
-- statement:
--   For $p\ge8$, $0<q\le19/40$, $159/50<K_p$, and $E_p(q)<K_p$, any strict real-three-dimensional counterexample has a normalized, oriented counterpart with singleton norm sum 3, total norm between 1 and $3q$, and each pair norm at most its assigned principal coordinate plus $1/200$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Generic norm and normalization proofs retain the Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff8.coarse_failure_reduction {p q : ℝ} (hp : 8 ≤ p)
    (hq0 : 0 < q) (hqcap : q ≤ 19/40)
    (hlinear : (159/50 : ℝ) < cyclicConstant p)
    (henvelope : scalarEnvelope p q < cyclicConstant p)
    (x y z : Fin 3 → ℝ) (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    ∃ X : Fin 3 → Fin 3 → ℝ,
      lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2) = 3 ∧
      1 ≤ lpNorm p (X 0+X 1+X 2) ∧
      lpNorm p (X 0+X 1+X 2) ≤ 3*q ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
        lpNorm p (X j+X k) ≤ X j i+X k i+1/200) ∧
      tripleDeficit p (cyclicConstant p) X < 0 := by sorry
