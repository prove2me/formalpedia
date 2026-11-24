-- Prove2me | Theorems.Thm_GlobalTheory_QuadFieldCriterion_isField_iff_no_residual_root
-- name    : GlobalTheory.QuadFieldCriterion.isField_iff_no_residual_root
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:09:54.689806+00:00
-- url     : https://prove2.me/theorems/d3ea8c34-6671-47e8-8ae8-a56510cb82ab
-- title:
--   Quad Field Criterion: is Field iff no residual root
-- statement:
--   The Quad Field Criterion construction uses the is Field iff no residual root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IsFieldIffNoResidualRoot.lean#L81-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IsFieldIffNoResidualRoot.lean#L81-L92

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_SelfDualUnramifiedPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IsFieldIffNoResidualRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory GlobalTheory.QuadFieldCriterion
open Polynomial IsLocalRing

theorem GlobalTheory.QuadFieldCriterion.isField_iff_no_residual_root : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (A : Type) [CommRing A] [Algebra (Fv F v) A] (w : A) (t n : v.adicCompletionIntegers F), IsUnit (t ^ 2 - 4 * n) → w ^ 2 - algebraMap (Fv F v) A t * w + algebraMap (Fv F v) A n = 0 → (∀ z : A, ∃ a b : Fv F v, z = algebraMap (Fv F v) A a + algebraMap (Fv F v) A b * w) → (∀ a b : Fv F v, algebraMap (Fv F v) A a + algebraMap (Fv F v) A b * w = 0 → a = 0 ∧ b = 0) → (IsField A ↔ ¬ ∃ r : IsLocalRing.ResidueField (v.adicCompletionIntegers F), r ^ 2 - IsLocalRing.residue (v.adicCompletionIntegers F) t * r + IsLocalRing.residue (v.adicCompletionIntegers F) n = 0) := by sorry
