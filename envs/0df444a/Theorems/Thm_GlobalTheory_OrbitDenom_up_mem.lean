-- Prove2me | Theorems.Thm_GlobalTheory_OrbitDenom_up_mem
-- name    : GlobalTheory.OrbitDenom.up_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:29:58.972864+00:00
-- url     : https://prove2.me/theorems/8cdfb7c6-1df2-4cf1-b86e-a61940e5464c
-- title:
--   Orbit Denom: up mem
-- statement:
--   The Orbit Denom construction uses the up mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LeadingMinorsProdDenominatorUnitriangularFactors.lean#L251-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LeadingMinorsProdDenominatorUnitriangularFactors.lean#L251-L280

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactors
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
open GlobalTheory GlobalTheory.OrbitDenom
variable {E : Type} [CommRing E]

theorem GlobalTheory.OrbitDenom.up_mem (O : Subring E) {n l' l : ℕ} (h : l ≤ n) (h' : l' ≤ n)
    (A W B : Matrix (Fin n) (Fin n) E)
    (hA : ∀ a k : Fin n, a < k → A a k = 0) (hA1 : ∀ a, A a a = 1)
    (hB : ∀ a k : Fin n, k < a → B a k = 0) (hB1 : ∀ a, B a a = 1)
    (hZ : ∀ a b, (A * W * B) a b ∈ O) (hW : IsUnit W.det)
    (hc : ∀ k b : Fin n, l' ≤ (k : ℕ) → (b : ℕ) < l' → W k b = 0)
    (hAO : ∀ a b : Fin n, (a : ℕ) < l → l' ≤ (b : ℕ) → A a b ∈ O)
    (t : E) (ε : Fin n → E) (hε : ∀ b, ε b ∈ O) (hε2 : ∀ b, ε b * ε b = 1)
    (hcol : ∀ a b : Fin n, l' ≤ (b : ℕ) → (b : ℕ) < l →
      W a b = (if (a : ℕ) + b + 1 = l + l' then t else 0) * ε b)
    (hrow : ∀ a b : Fin n, l' ≤ (a : ℕ) → (a : ℕ) < l →
      W a b = (if (a : ℕ) + b + 1 = l + l' then t else 0) * ε b)
    (i : Fin n) (hi' : l' ≤ (i : ℕ)) (hi : (i : ℕ) < l) (j : Fin n) :
    (W.submatrix (Fin.castLE h) (Fin.castLE h)).det *
      (W.submatrix (Fin.castLE h') (Fin.castLE h')).det * B i j ∈ O := by sorry
