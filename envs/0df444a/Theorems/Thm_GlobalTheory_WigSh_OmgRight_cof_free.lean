-- Prove2me | Theorems.Thm_GlobalTheory_WigSh_OmgRight_cof_free
-- name    : GlobalTheory.WigSh.OmgRight.cof_free
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:45:01.915543+00:00
-- url     : https://prove2.me/theorems/7c5f1ce1-fa25-5ef4-9e58-0127df455aa7
-- title:
--   Omg Right: cof free
-- statement:
--   The Omg Right construction uses the cof free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/HpkConjTranspose.lean#L95-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/HpkConjTranspose.lean#L95-L115

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

theorem GlobalTheory.WigSh.OmgRight.cof_free (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mx k r) (a : Fin r) :
    ((Hpk k r * gᴴ * Hpk k r) *ᵥ
      ∑ c, star ((Zhat k r z z' g).adjugate (Fin.last r) c) • fvec k r z c) (esI k r a) = 0 := by sorry
