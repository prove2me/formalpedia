-- Prove2me | Theorems.Thm_GlobalTheory_CycEigen_twAct_fixed_eq_zero
-- name    : GlobalTheory.CycEigen.twAct_fixed_eq_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:25:33.750547+00:00
-- url     : https://prove2.me/theorems/c6b2ee5f-45a2-416f-97e6-0142e2189693
-- title:
--   Cyc Eigen: tw Act fixed eq zero
-- statement:
--   The Cyc Eigen construction uses the tw Act fixed eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormZpowSubOneLeBis.lean#L213-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormZpowSubOneLeBis.lean#L213-L250

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLeBis
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
variable {l : ℕ} [hl : Fact l.Prime]

theorem GlobalTheory.CycEigen.twAct_fixed_eq_zero {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)}
    {χ : GQ l →* ℚ_[l]ˣ} (hact : IsActC act) (hχ : IsCyc χ) {K : FinExt l} {j : ℕ} (hj : Lev l j)
    {g : GQ l} (hg : IsGen χ K j g) {r : ℕ} (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l))
    (hU : ∀ a b, U g a b ∈ intC (Ks K j)) (hU1 : ∀ a b, ‖(U g - 1) a b‖ < rho1 l) (i : ℤ)
    (y : Fin r → PadicComplex l) (hy : ∀ a, y a ∈ Xj K j) (hfix : twAct act χ i U g y = y) :
    y = 0 := by sorry
