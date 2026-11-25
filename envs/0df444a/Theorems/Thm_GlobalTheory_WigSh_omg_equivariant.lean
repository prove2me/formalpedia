-- Prove2me | Theorems.Thm_GlobalTheory_WigSh_omg_equivariant
-- name    : GlobalTheory.WigSh.omg_equivariant
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:34:46.268426+00:00
-- url     : https://prove2.me/theorems/8181c576-b51f-43a0-b58d-9775bf070c3e
-- title:
--   Wig Sh: omg equivariant
-- statement:
--   The Wig Sh construction uses the omg equivariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/OmgEquivariant.lean#L238-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/OmgEquivariant.lean#L238-L257

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
open GlobalTheory GlobalTheory.WigSh
open OmgEquiv

theorem GlobalTheory.WigSh.omg_equivariant : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g h h' : Mx k r), inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → g ∈ UH (Hpk k r) → h ∈ UWset k r z → h' ∈ UWset k r z' → GlobalTheory.WigSh.omg k r z z' (h⁻¹ * g * h') = h'⁻¹ *ᵥ GlobalTheory.WigSh.omg k r z z' g := by sorry
