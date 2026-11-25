-- Prove2me | Theorems.Thm_GlobalTheory_WigSh_omg_mul_N
-- name    : GlobalTheory.WigSh.omg_mul_N
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:55:53.575327+00:00
-- url     : https://prove2.me/theorems/7bb36a55-42bc-56e0-8011-1e9431584b4c
-- title:
--   Wig Sh: omg mul N
-- statement:
--   The Wig Sh construction uses the omg mul N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/HpkConjTranspose.lean#L258-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/HpkConjTranspose.lean#L258-L282

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_WigMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingMinorInvariant
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_NilpotentSubgroup
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CasimirSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_HpkConjTranspose
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
open GlobalTheory.LeadingMinorInv
open OmgRight
open Matrix

theorem GlobalTheory.WigSh.omg_mul_N : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ))
    (g m : _root_.Formalism.FourierDecayAlt.Q.Mx k r), _root_.Formalism.QuantumDeterminants.inWb k r z → _root_.Formalism.QuantumDeterminants.inWb k r z' →
    g ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk k r) → m ∈ _root_.Formalism.QuantumDeterminants.Nset k r →
    _root_.GlobalTheory.WigSh.omg k r z z' (g * m) = _root_.GlobalTheory.WigSh.omg k r z z' g := by sorry
