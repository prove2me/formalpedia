-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsBaseChangeAt_comp
-- name    : GroundTheory.Arith.SchemeCoh.IsBaseChangeAt.comp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:11:23.012227+00:00
-- url     : https://prove2.me/theorems/361dc926-7e61-4add-85e5-b47aba8e336b
-- title:
--   Is Base Change At: comp
-- statement:
--   The Is Base Change At construction uses the comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/PullbackBaseChange.lean#L36-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/PullbackBaseChange.lean#L36-L101

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_PullbackAffine
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohZariski
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_PullbackBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits
universe u
noncomputable section
variable {W T U : Scheme.{u}}

theorem GroundTheory.Arith.SchemeCoh.IsBaseChangeAt.comp {f : W ⟶ T} {g : T ⟶ U} {N : U.Modules} {O : U.Opens}
    (hg : IsBaseChangeAt g N O)
    (hf : IsBaseChangeAt f ((Scheme.Modules.pullback g).obj N) (g ⁻¹ᵁ O)) :
    IsBaseChangeAt (f ≫ g) N O := by sorry
