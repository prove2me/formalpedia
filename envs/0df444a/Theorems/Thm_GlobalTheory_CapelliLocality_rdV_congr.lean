-- Prove2me | Theorems.Thm_GlobalTheory_CapelliLocality_rdV_congr
-- name    : GlobalTheory.CapelliLocality.rdV_congr
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:29:18.34608+00:00
-- url     : https://prove2.me/theorems/8c364e0c-d2f9-442b-9cdc-75272d633caa
-- title:
--   Capelli Locality: rd V congr
-- statement:
--   The Capelli Locality construction uses the rd V congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CapelliOperatorUnitaryGroupLocal.lean#L31-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CapelliOperatorUnitaryGroupLocal.lean#L31-L40

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_Smooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CapelliOperatorUnitaryGroupLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open GlobalTheory GlobalTheory.CapelliLocality
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem GlobalTheory.CapelliLocality.rdV_congr (H K X : Matrix (Fin n) (Fin n) ℂ) (hKH : K * H = 1) (hHK : H * K = 1)
    (hX : Xᴴ * H = -(H * X)) {F₁ F₂ : Matrix (Fin n) (Fin n) ℂ → E}
    (hF : ∀ x, inUH H x → F₁ x = F₂ x) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUH H g) :
    RdV X F₁ g = RdV X F₂ g := by sorry
