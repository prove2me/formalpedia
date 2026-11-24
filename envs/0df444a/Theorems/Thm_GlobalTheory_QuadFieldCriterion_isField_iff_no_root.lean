-- Prove2me | Theorems.Thm_GlobalTheory_QuadFieldCriterion_isField_iff_no_root
-- name    : GlobalTheory.QuadFieldCriterion.isField_iff_no_root
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:10:09.722296+00:00
-- url     : https://prove2.me/theorems/128f1103-f661-4557-861b-27ba2c9c1c52
-- title:
--   Quad Field Criterion: is Field iff no root
-- statement:
--   The Quad Field Criterion construction uses the is Field iff no root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IsFieldIffNoResidualRoot.lean#L42-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IsFieldIffNoResidualRoot.lean#L42-L79

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

theorem GlobalTheory.QuadFieldCriterion.isField_iff_no_root {K A : Type*} [Field K] [CommRing A] [Algebra K A] (w : A) (t n : K)
    (hw : w ^ 2 - algebraMap K A t * w + algebraMap K A n = 0)
    (hspan : ∀ z : A, ∃ a b : K, z = algebraMap K A a + algebraMap K A b * w)
    (hind : ∀ a b : K, algebraMap K A a + algebraMap K A b * w = 0 → a = 0 ∧ b = 0) :
    IsField A ↔ ¬ ∃ x : K, x ^ 2 - t * x + n = 0 := by sorry
