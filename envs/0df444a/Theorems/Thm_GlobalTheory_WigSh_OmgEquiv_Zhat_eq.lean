-- Prove2me | Theorems.Thm_GlobalTheory_WigSh_OmgEquiv_Zhat_eq
-- name    : GlobalTheory.WigSh.OmgEquiv.Zhat_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:39:04.451815+00:00
-- url     : https://prove2.me/theorems/e1fb1de2-88ab-5875-b75a-88f53b0c1130
-- title:
--   Omg Equiv: Zhat eq
-- statement:
--   The Omg Equiv construction uses the Zhat eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/OmgEquivariant.lean#L217-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/OmgEquivariant.lean#L217-L230

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

theorem GlobalTheory.WigSh.OmgEquiv.Zhat_eq {g h h' : Mx k r} (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z') :
    Zhat k r z z' (h⁻¹ * g * h') = Zhat k r z z' g := by sorry
