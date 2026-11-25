-- Prove2me | Theorems.Thm_GlobalTheory_exists_form_of_compatible_fractions
-- name    : GlobalTheory.exists_form_of_compatible_fractions
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:41:09.098149+00:00
-- url     : https://prove2.me/theorems/b34ec8a8-8cd3-479c-93af-139576123529
-- title:
--   Global Theory: exists form of compatible fractions
-- statement:
--   The Global Theory construction uses the exists form of compatible fractions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFormOfCompatibleFractions.lean#L45-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFormOfCompatibleFractions.lean#L45-L145

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexGradedModuleExactAtOfLargeDegree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFormOfCompatibleFractions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial
open GlobalTheory

theorem GlobalTheory.exists_form_of_compatible_fractions : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (n : ℕ) (J : Ideal (MvPolynomial (Fin (n + 1)) A)), (∀ F ∈ J, ∀ d, homogeneousComponent d F ∈ J) → ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ (N : ℕ) (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) A), (∀ i, (F i).IsHomogeneous (d + N)) → (∀ i j, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) A) * X j) ^ L * (X j ^ N * F i - X i ^ N * F j) ∈ J) → ∃ G : MvPolynomial (Fin (n + 1)) A, G.IsHomogeneous d ∧ ∀ i, ∃ L : ℕ, (X i : MvPolynomial (Fin (n + 1)) A) ^ L * (F i - X i ^ N * G) ∈ J := by sorry
