-- Prove2me | Theorems.Thm_GlobalTheory_WigSh_OmgRight_prW_mulVec
-- name    : GlobalTheory.WigSh.OmgRight.prW_mulVec
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:48:46.683815+00:00
-- url     : https://prove2.me/theorems/93272038-8610-4eb2-9bf9-ed2f794c24bc
-- title:
--   Omg Right: pr W mul Vec
-- statement:
--   The Omg Right construction uses the pr W mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/HpkConjTranspose.lean#L67-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/HpkConjTranspose.lean#L67-L93

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
open GlobalTheory.WigSh.OmgRight

theorem GlobalTheory.WigSh.OmgRight.prW_mulVec {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) {n : Mx k r} (hn : n ∈ Formalism.QuantumDeterminants.Nset k r)
    {v : Fin (2 * r + k + 1) → ℂ} (hv : ∀ a : Fin r, v (esI k r a) = 0) :
    Formalism.FourierDecayAlt.D.prW k r z (n *ᵥ v) = Formalism.FourierDecayAlt.D.prW k r z v := by sorry
