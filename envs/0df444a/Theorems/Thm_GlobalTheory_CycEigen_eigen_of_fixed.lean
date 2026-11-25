-- Prove2me | Theorems.Thm_GlobalTheory_CycEigen_eigen_of_fixed
-- name    : GlobalTheory.CycEigen.eigen_of_fixed
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:33:46.731241+00:00
-- url     : https://prove2.me/theorems/875e02e0-0d3b-4ef0-865e-3dc66d2c3501
-- title:
--   Cyc Eigen: eigen of fixed
-- statement:
--   The Cyc Eigen construction uses the eigen of fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AevalProdEqZeroHodgeTateCyclotomicFrame.lean#L108-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AevalProdEqZeroHodgeTateCyclotomicFrame.lean#L108-L134

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLeBis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerFixedIffMemCompletedIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AevalProdEqZeroHodgeTateCyclotomicFrame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CycEigen
variable {l : ℕ} [Fact l.Prime]

theorem GlobalTheory.CycEigen.eigen_of_fixed {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)}
    {χ : GQ l →* ℚ_[l]ˣ} (hact : IsActC act) (hχ : IsCyc χ) {K : FinExt l} {m r : ℕ}
    (hm : Lev l m) {U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)} {g : GQ l}
    (hF : Frame χ K m U g) (u : ℤ) (y : Fin r → PadicComplex l)
    (hy : ∀ σ ∈ Gj K m, twAct act χ u U σ y = y) : (U g).mulVec y = chiC χ (-u) g • y := by sorry
