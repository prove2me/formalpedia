-- Prove2me | Theorems.Thm_MainStatements_BetaInf_decay_J
-- name    : MainStatements.BetaInf.decay_J
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:37:10.328873+00:00
-- url     : https://prove2.me/theorems/81f3b252-506c-55a4-8d22-f4a2b048c110
-- title:
--   Beta Inf: decay J
-- statement:
--   The Beta Inf construction uses the decay J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/KFiniteVectors/KDecay.lean#L33-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/KFiniteVectors/KDecay.lean#L33-L79

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousMulMt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerSmoothStability_ExistsFinStableOfMemSSup
import Definitions.Def_CompanionTheory_AutomorphicTheory_KFiniteVectors_KDecay
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MainStatements MainStatements.BetaInf
open Formalism.FourierDecayAlt PI.UpqRep Matrix CompanionTheory.LimBd.Main
open scoped InnerProductSpace
noncomputable section

theorem MainStatements.BetaInf.decay_J {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} (hZ : ZuckT t) {n : ℕ} (ε : Fin n → Bool) :
    ∀ (m : ℕ) (h : ℝ) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCParam μ → IsDS ε μ σ → PI.ZuckTensor.GapAtLeast ε μ h →
      t n ε + m < h → ∀ v w : H, IsKFin ε σ v → IsKFin ε σ w →
      ∃ C : ℝ, ∀ g ∈ UJset ε, sN g ^ m * ‖⟪w, σ g v⟫_ℂ‖ ≤ C := by sorry
