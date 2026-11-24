-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_IsContOn_of_isLocallyConstant
-- name    : GlobalTheory.WeilM.IsContOn.of_isLocallyConstant
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:53:57.210041+00:00
-- url     : https://prove2.me/theorems/1eb308c1-5ea2-49fd-82a6-885b41666e32
-- title:
--   Is Cont On: of is Locally Constant
-- statement:
--   The Is Cont On construction uses the of is Locally Constant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean#L65-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean#L65-L67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped NNReal Classical
open GlobalTheory GlobalTheory.WeilM
variable {R : Type} [CommRing R] {κ : Type} [Fintype κ] {G : Type} [Group G]

theorem GlobalTheory.WeilM.IsContOn.of_isLocallyConstant [TopologicalSpace G] {C : TestClass R} {om : G →* Module.End ℂ ((κ → R) → ℂ)}
    (h : ∀ φ ∈ C.sp κ, IsLocallyConstant fun g => om g φ) : IsContOn C om := by sorry
