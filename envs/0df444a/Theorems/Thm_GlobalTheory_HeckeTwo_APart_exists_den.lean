-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_APart_exists_den
-- name    : GlobalTheory.HeckeTwo.APart.exists_den
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:01:41.637451+00:00
-- url     : https://prove2.me/theorems/20bf6141-023b-4b14-a501-2ab6e3e9a736
-- title:
--   APart: exists den
-- statement:
--   The APart construction uses the exists den property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeEisensteinConstantTermPartDifferentiableOn.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeEisensteinConstantTermPartDifferentiableOn.lean#L16-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinConstantTermPartDifferentiableOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.APart
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.HeckeTwo.APart.exists_den (I : FractionalIdeal (𝓞 F)⁰ F) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ b ∈ I, ∃ x : 𝓞 F, (x : F) = (d : F) * b := by sorry
