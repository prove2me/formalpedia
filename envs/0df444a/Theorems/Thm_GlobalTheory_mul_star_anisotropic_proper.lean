-- Prove2me | Theorems.Thm_GlobalTheory_mul_star_anisotropic_proper
-- name    : GlobalTheory.mul_star_anisotropic_proper
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:11:55.491395+00:00
-- url     : https://prove2.me/theorems/4d5ccb04-5223-43ad-9a9f-794e72349520
-- title:
--   Global Theory: mul star anisotropic proper
-- statement:
--   The Global Theory construction uses the mul star anisotropic proper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsCompactPreimageMulStarAnisotropicSubmodule.lean#L7-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsCompactPreimageMulStarAnisotropicSubmodule.lean#L7-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCompactPreimageMulStarAnisotropicSubmodule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix
open GlobalTheory

theorem GlobalTheory.mul_star_anisotropic_proper : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (V : Submodule E (Matrix (Fin r) (Fin r) E)), (∀ z ∈ V, z * star z = 0 → z = 0) → ∀ B : Set (Matrix (Fin r) (Fin r) E), IsCompact B → IsCompact {z : Matrix (Fin r) (Fin r) E | z ∈ V ∧ z * star z ∈ B} := by sorry
