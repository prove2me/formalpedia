-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_continuous_galTateRep
-- name    : GroundTheory.Arith.Abelian.continuous_galTateRep
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:52:45.715601+00:00
-- url     : https://prove2.me/theorems/ae55ca86-48cd-5a26-81d2-4c00e7ce625b
-- title:
--   Abelian: continuous gal Tate Rep
-- statement:
--   The Abelian construction uses the continuous gal Tate Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TateModule.lean#L427-L431
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TateModule.lean#L427-L431

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TorsionGalois
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TateModule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open AddSubgroup
universe u
variable (K L : Type u) [Field K] [Field L] [Algebra K L] [DecidableEq L] (W : WeierstrassCurve K)
  (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

theorem GroundTheory.Arith.Abelian.continuous_galTateRep [Algebra.IsIntegral K L] :
    Continuous (fun p : Gal(L/K) × TateModule ℓ (W.baseChange L).toAffine.Point =>
      galTateRep K L W ℓ p.1 p.2) := by sorry
