-- Prove2me | Theorems.Thm_GlobalTheory_WigSh_OmgEquiv_herm_UH
-- name    : GlobalTheory.WigSh.OmgEquiv.herm_UH
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:35:37.908809+00:00
-- url     : https://prove2.me/theorems/a7ae0511-047b-57a5-a500-3d5bfd2f9a8f
-- title:
--   Omg Equiv: herm UH
-- statement:
--   The Omg Equiv construction uses the herm UH property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/OmgEquivariant.lean#L17-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/OmgEquivariant.lean#L17-L22

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

theorem GlobalTheory.WigSh.OmgEquiv.herm_UH {h : Mx k r} (hh : h ∈ UH (Hpk k r)) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (h *ᵥ v) (h *ᵥ w) = herm (Hpk k r) v w := by sorry
