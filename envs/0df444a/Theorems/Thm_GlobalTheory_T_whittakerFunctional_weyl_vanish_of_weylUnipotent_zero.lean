-- Prove2me | Theorems.Thm_GlobalTheory_T_whittakerFunctional_weyl_vanish_of_weylUnipotent_zero
-- name    : GlobalTheory.T.whittakerFunctional_weyl_vanish_of_weylUnipotent_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:01:12.593504+00:00
-- url     : https://prove2.me/theorems/b72d4afb-15f4-4f25-9fa1-32ff7ef90b76
-- title:
--   T: whittaker Functional weyl vanish of weyl Unipotent zero
-- statement:
--   The T construction uses the whittaker Functional weyl vanish of weyl Unipotent zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WhittakerFunctionalWeylVanishOfWeylUnipotentZeroStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WhittakerFunctionalWeylVanishOfWeylUnipotentZeroStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WhittakerFunctionalWeylVanishOfWeylUnipotentZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WhittakerFunctionalWeylVanishOfWeylUnipotentZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.whittakerFunctional_weyl_vanish_of_weylUnipotent_zero : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ Ψ : SpecialLinearGroup (Fin 2) A.K → ℂ, A.InI Ψ → (∀ z, Ψ (wS A.K * nS z) = 0) → ∀ (a : A.K) (c : F), A.abelian₂ μK ψ a (fun h => Ψ (h * wS A.K)) c = 0 := by sorry
