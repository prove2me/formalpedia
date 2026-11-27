-- Prove2me | Theorems.Thm_MainStatements_BetaInf_isKFinHpk_of_low
-- name    : MainStatements.BetaInf.isKFinHpk_of_low
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:03:55.993705+00:00
-- url     : https://prove2.me/theorems/aaf197a6-76eb-581e-83da-9b53768bd051
-- title:
--   Beta Inf: is KFin Hpk of low
-- statement:
--   The Beta Inf construction uses the is KFin Hpk of low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/KFiniteVectors/KDecay.lean#L148-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/KFiniteVectors/KDecay.lean#L148-L158

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

theorem MainStatements.BetaInf.isKFinHpk_of_low {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : B.Mat k r → (H →L[ℂ] H)} {Q : B.Mat k r}
    (hQ : IsCayleyU k r ε Q) {w : H} (hw : w ∈ lowKSub ε lam (fun g => σ (Q⁻¹ * g * Q))) :
    IsKFinHpk (k := k) (r := r) σ w := by sorry
