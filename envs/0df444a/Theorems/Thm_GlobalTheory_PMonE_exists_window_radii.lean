-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_exists_window_radii
-- name    : GlobalTheory.PMonE.exists_window_radii
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:38:44.416805+00:00
-- url     : https://prove2.me/theorems/fbb7a505-d1d5-44b6-a731-cb731b171003
-- title:
--   PMon E: exists window radii
-- statement:
--   The PMon E construction uses the exists window radii property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsWindowRadii.lean#L8-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsWindowRadii.lean#L8-L93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsWindowRadii
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PMonE
open Finset

theorem GlobalTheory.PMonE.exists_window_radii : ∀ (F : Type) [NontriviallyNormedField F]
    [IsUltrametricDist F] [IsAlgClosed F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
    (k : ℕ) (ϖ : F), ‖ϖ‖ = (p : ℝ)⁻¹ → ∀ lam : Fin (k + 1) → F, (∀ j, lam j ≠ 0) →
    Antitone (fun j => ‖lam j‖) → (∀ i j, ‖lam i‖ < p * ‖lam j‖) →
    ∃ π : Fin (k + 1) → F, (∀ j, π j ≠ 0 ∧ ‖π j‖ < 1) ∧
      (∀ j : Fin k, ‖lam j.succ‖ * ‖π j.succ‖ ^ p ^ (j : ℕ) =
        ‖lam j.castSucc‖ * ‖π j.castSucc‖ ^ p ^ (j : ℕ)) ∧
      (‖lam 0‖ / p) ^ p * ‖π 0‖ = (‖lam (Fin.last k)‖ * ‖π (Fin.last k)‖ ^ p ^ k) ^ p := by sorry
