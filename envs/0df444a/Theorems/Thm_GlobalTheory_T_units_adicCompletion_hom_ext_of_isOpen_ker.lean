-- Prove2me | Theorems.Thm_GlobalTheory_T_units_adicCompletion_hom_ext_of_isOpen_ker
-- name    : GlobalTheory.T.units_adicCompletion_hom_ext_of_isOpen_ker
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:00:52.338993+00:00
-- url     : https://prove2.me/theorems/8fba2424-6369-46f1-a32a-a457affe9b74
-- title:
--   T: units adic Completion hom ext of is Open ker
-- statement:
--   The T construction uses the units adic Completion hom ext of is Open ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitsAdicCompletionHomExtOfIsOpenKerStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitsAdicCompletionHomExtOfIsOpenKerStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitsAdicCompletionHomExtOfIsOpenKer
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitsAdicCompletionHomExtOfIsOpenKerStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.units_adicCompletion_hom_ext_of_isOpen_ker : ∀ (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (B : Type) [Group B] (f g : (v.adicCompletion F)ˣ →* B), IsOpen (f.ker : Set (v.adicCompletion F)ˣ) → IsOpen (g.ker : Set (v.adicCompletion F)ˣ) → (∀ c : Fˣ, f (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom c) = g (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom c)) → ∀ x, f x = g x := by sorry
