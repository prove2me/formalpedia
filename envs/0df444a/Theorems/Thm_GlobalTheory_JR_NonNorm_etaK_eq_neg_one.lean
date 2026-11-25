-- Prove2me | Theorems.Thm_GlobalTheory_JR_NonNorm_etaK_eq_neg_one
-- name    : GlobalTheory.JR.NonNorm.etaK_eq_neg_one
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:59:11.509276+00:00
-- url     : https://prove2.me/theorems/69c62ab9-3f1f-46c5-ae2b-dbc314a6d6af
-- title:
--   Non Norm: eta K eq neg one
-- statement:
--   The Non Norm construction uses the eta K eq neg one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EtaKEqNegOneOfNotNorm.lean#L82-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EtaKEqNegOneOfNotNorm.lean#L82-L147

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNormSurj
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaKEqNegOneOfNotNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.NonNorm
open ValuativeRel GroundTheory.LocalField IntermediateField

theorem GlobalTheory.JR.NonNorm.etaK_eq_neg_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → IsField A.L → ∀ s : A.Kˣ, (¬ ∃ y : A.L, A.NL y = s) → A.etaK s = -1 := by sorry
