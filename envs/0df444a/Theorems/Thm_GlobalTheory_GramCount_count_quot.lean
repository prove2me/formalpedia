-- Prove2me | Theorems.Thm_GlobalTheory_GramCount_count_quot
-- name    : GlobalTheory.GramCount.count_quot
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:31:54.721073+00:00
-- url     : https://prove2.me/theorems/95dafb1f-3a8e-51be-a65c-68a64161d26c
-- title:
--   Gram Count: count quot
-- statement:
--   The Gram Count construction uses the count quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardPrimitiveTuplesHermitianGramModUniformizer.lean#L50-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardPrimitiveTuplesHermitianGramModUniformizer.lean#L50-L191

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveTuplesWithGramMatrixHenselCountStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NcardPrimitiveTuplesGramModNilpotentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianMatricesDvdSqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NcardPrimitiveTuplesWithGramMatrixResidueRingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardPrimitiveTuplesHermitianGramModUniformizer
import Theorems.Thm_GlobalTheory_GramCount_Prim_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.GramCount
variable {O : Type} [CommRing O]

theorem GlobalTheory.GramCount.count_quot (c : O →+* O) (hc : ∀ u, c (c u) = u) (ω : O) (hω : IsUnit (ω - c ω))
    (p : O) (hp : c p = p) (hK : ∀ t, c t = t → ¬ p ∣ t → IsUnit t) (q : ℕ) (hq : 2 ≤ q)
    (j : ℕ) (hj : 1 ≤ j) (h1 : Nat.card (O ⧸ Ideal.span {p}) = q ^ 2)
    (h2 : Nat.card (O ⧸ Ideal.span {p ^ j}) = q ^ (2 * j)) (hpj : c (p ^ j) = p ^ j)
    (m n : ℕ) (hmn : 2 * m + 3 ≤ n) (G : Matrix (Fin m) (Fin m) O)
    (hG : ∀ a b, c (G b a) = G a b) (N : ℕ)
    (hN : N = Set.ncard (sols (quotInv c (p ^ j) hpj) n (G.map (Ideal.Quotient.mk _)))) :
    (q : ℝ) ^ (j * (2 * n * m - m ^ 2)) ≤ 2 * N ∧
      (N : ℝ) ≤ 2 * (q : ℝ) ^ (j * (2 * n * m - m ^ 2)) := by sorry
