-- Prove2me | Theorems.Thm_GlobalTheory_WigSh_OmgEquiv_prW_comm
-- name    : GlobalTheory.WigSh.OmgEquiv.prW_comm
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:35:49.200344+00:00
-- url     : https://prove2.me/theorems/b43879bc-abd8-42ce-ad5b-1f5adc1a4315
-- title:
--   Omg Equiv: pr W comm
-- statement:
--   The Omg Equiv construction uses the pr W comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/OmgEquivariant.lean#L205-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/OmgEquivariant.lean#L205-L215

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_WigMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_OmgEquivariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
noncomputable section
open GlobalTheory GlobalTheory.WigSh GlobalTheory.WigSh.OmgEquiv
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ}

theorem GlobalTheory.WigSh.OmgEquiv.prW_comm {h : Mx k r} (hh : h ∈ UWset k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    Formalism.FourierDecayAlt.D.prW k r z (h *ᵥ v) = h *ᵥ Formalism.FourierDecayAlt.D.prW k r z v := by sorry
