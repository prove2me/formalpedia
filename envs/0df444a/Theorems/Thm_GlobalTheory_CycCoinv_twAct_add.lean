-- Prove2me | Theorems.Thm_GlobalTheory_CycCoinv_twAct_add
-- name    : GlobalTheory.CycCoinv.twAct_add
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:55:31.31481+00:00
-- url     : https://prove2.me/theorems/82331884-6c77-5cc9-a189-75c78ac932fe
-- title:
--   Cyc Coinv: tw Act add
-- statement:
--   The Cyc Coinv construction uses the tw Act add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TorsionCoinvariantsTwistedCyclotomicGenerator.lean#L166-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TorsionCoinvariantsTwistedCyclotomicGenerator.lean#L166-L173

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLeTer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AevalProdEqZeroHodgeTateCyclotomicFrameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorsionCoinvariantsTwistedCyclotomicGenerator
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

theorem GlobalTheory.CycCoinv.twAct_add (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ) (i : ℤ)
    {r : ℕ} (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l)
    (x y : Fin r → PadicComplex l) :
    twAct act χ i U g (x + y) = twAct act χ i U g x + twAct act χ i U g y := by sorry
