-- Prove2me | Theorems.Thm_GlobalTheory_WigSh_OmLeftN_omg_left_N
-- name    : GlobalTheory.WigSh.OmLeftN.omg_left_N
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:00:39.44566+00:00
-- url     : https://prove2.me/theorems/c2592a9f-d92b-55fb-a420-58c8586532c0
-- title:
--   Om Left N: omg left N
-- statement:
--   The Om Left N construction uses the omg left N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/OmgMulLeft.lean#L87-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/OmgMulLeft.lean#L87-L88

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_WigMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_NilpotentSubgroup
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CasimirSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingMinorInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_OmgMulLeft
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
open GlobalTheory GlobalTheory.WigSh GlobalTheory.WigSh.OmLeftN

theorem GlobalTheory.WigSh.OmLeftN.omg_left_N : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g m : Mx k r), inWb k r z → inWb k r z' → g ∈ UH (Hpk k r) → m ∈ Formalism.QuantumDeterminants.Nset k r → GlobalTheory.WigSh.omg k r z z' (m⁻¹ * g) = GlobalTheory.WigSh.omg k r z z' g := by sorry
