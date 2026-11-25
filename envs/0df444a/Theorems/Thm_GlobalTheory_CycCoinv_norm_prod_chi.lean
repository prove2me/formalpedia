-- Prove2me | Theorems.Thm_GlobalTheory_CycCoinv_norm_prod_chi
-- name    : GlobalTheory.CycCoinv.norm_prod_chi
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:56:17.33081+00:00
-- url     : https://prove2.me/theorems/aaeb7675-f449-46a4-ac05-5d39abc440d4
-- title:
--   Cyc Coinv: norm prod chi
-- statement:
--   The Cyc Coinv construction uses the norm prod chi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TorsionCoinvariantsTwistedCyclotomicGenerator.lean#L143-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TorsionCoinvariantsTwistedCyclotomicGenerator.lean#L143-L156

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

theorem GlobalTheory.CycCoinv.norm_prod_chi {χ : GQ l →* ℚ_[l]ˣ} {K : FinExt l} {j : ℕ} (hj : Lev l j) {g : GQ l}
    (hg : IsGen χ K j g) (J : Finset ℤ) (i : ℤ) :
    ‖∏ u ∈ J.erase i, ((χ g : ℚ_[l]) ^ (-i) - (χ g : ℚ_[l]) ^ (-u))‖
      = ((l : ℝ)⁻¹) ^ (∑ u ∈ J.erase i, (j + padicValInt l (u - i))) := by sorry
