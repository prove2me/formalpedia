-- Prove2me | Theorems.Thm_GlobalTheory_CycCoinv_Ks_le_Kinf
-- name    : GlobalTheory.CycCoinv.Ks_le_Kinf
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:55:22.342185+00:00
-- url     : https://prove2.me/theorems/d1ef668f-1e86-5310-aa77-d010732af4ae
-- title:
--   Cyc Coinv: Ks le Kinf
-- statement:
--   The Cyc Coinv construction uses the Ks le Kinf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TorsionCoinvariantsTwistedCyclotomicGenerator.lean#L82-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TorsionCoinvariantsTwistedCyclotomicGenerator.lean#L82-L84

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLeTer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AevalProdEqZeroHodgeTateCyclotomicFrameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorsionCoinvariantsTwistedCyclotomicGenerator
import Theorems.Thm_GlobalTheory_Cyc_AlmostTrace_Ks_le_Kinf
import Theorems.Thm_GlobalTheory_TateDecomp_Ks_le_Kinf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
open GlobalTheory GlobalTheory.CycCoinv
variable {l : ℕ} [hl : Fact l.Prime]

theorem GlobalTheory.CycCoinv.Ks_le_Kinf (K : FinExt l) (j : ℕ) : Ks K j ≤ Kinf K := by sorry
