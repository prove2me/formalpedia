-- Prove2me | Theorems.Thm_GlobalTheory_cloud_node_projector_bound
-- name    : GlobalTheory.cloud_node_projector_bound
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:47:28.745793+00:00
-- url     : https://prove2.me/theorems/6bac8636-0e20-5cfb-b601-1540c8d65c6e
-- title:
--   Global Theory: cloud node projector bound
-- statement:
--   The Global Theory construction uses the cloud node projector bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CloudNodeProjectionNormLowLevel.lean#L17-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CloudNodeProjectionNormLowLevel.lean#L17-L92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CardFilterFinBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CardFilterLeSuccAndSqSumLePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NormEigenLePowMulNormSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SplitCasEigenvalueSummand
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitaryGlModuleProjComponentsLevelAddTwoStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SplitCasimirResolventCircleBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_LevSubspaceMono
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NormSumEigenprojectorLeOfResolventBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CloudNodeProjectionNormLowLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
open GlobalTheory

theorem GlobalTheory.cloud_node_projector_bound (H : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] (n kk : ℕ) (bv : ℝ)
    (VV : Submodule ℂ H) (T : H →ₗ[ℂ] H) (p : Fin n → H →ₗ[ℂ] H) (lam : Fin n → ℝ)
    (hfd : FiniteDimensional ℂ VV) (hb : 0 < bv)
    (hsum : ∀ x, ∑ i, p i x = x)
    (hp : ∀ i, ∀ x ∈ VV, p i x ∈ VV ∧ T (p i x) = (lam i : ℂ) • p i x)
    (hpos : ∀ a : Fin n, (a.val + 1 < kk → -bv / 8 - bv / 32 ≤ lam a ∧ lam a ≤ bv / 32) ∧
      (kk ≤ a.val + 1 → bv - bv / 32 ≤ lam a ∧ lam a ≤ 2 * bv + bv / 32))
    (hgap : ∀ a c : Fin n, a ≠ c → 1 ≤ |lam a - lam c|)
    (hcard : (univ.filter fun a : Fin n => kk ≤ a.val + 1).card = n + 1 - kk)
    (hres : ∀ ζ : ℂ, ‖ζ + ((bv / 16 : ℝ) : ℂ)‖ = 9 * bv / 16 → ∀ x ∈ VV, 13 * bv / 32 * ‖x‖ ≤ ‖ζ • x - T x‖)
    (hT : ∀ x ∈ VV, ‖T x‖ ≤ 3 * bv * ‖x‖) :
    ∀ x ∈ VV, ‖∑ s ∈ univ.filter (fun a : Fin n => a.val + 1 < kk), p s x‖ ≤ 18 / 13 * ‖x‖ ∧
      ∀ s : Fin n, kk ≤ s.val + 1 → ‖p s x‖ ≤ 3 * (6 * bv) ^ (n - kk) * ‖x‖ := by sorry
