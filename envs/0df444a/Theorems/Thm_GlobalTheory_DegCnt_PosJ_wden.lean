-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_PosJ_wden
-- name    : GlobalTheory.DegCnt.PosJ.wden
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:53:49.796703+00:00
-- url     : https://prove2.me/theorems/a05ecf71-86f5-4ab8-8e43-409b9ec1d9d9
-- title:
--   Pos J: wden
-- statement:
--   The Pos J construction uses the wden property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormFlagLatticesNearUnderStabiliser.lean#L86-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormFlagLatticesNearUnderStabiliser.lean#L86-L151

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesPairingStabilizerBlockDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormFlagLatticesNearUnderStabiliser
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.PosJ
open LaurentPolynomial
variable {K : Type} [Field K]

theorem GlobalTheory.DegCnt.PosJ.wden (I : ℤ → AddSubgroup K) (h1 : (1 : K) ∈ I 0)
    (hmul : ∀ m n x y, x ∈ I m → y ∈ I n → x * y ∈ I (m + n)) {n l' l : ℕ} (h : l ≤ n) (h' : l' ≤ n)
    (r : ℤ) (k : Fin n → ℤ) (hk : ∀ a, k a = r - (a : ℕ)) (A W B : Matrix (Fin n) (Fin n) K)
    (hA : ∀ a k : Fin n, a < k → A a k = 0) (hA1 : ∀ a, A a a = 1)
    (hB : ∀ a k : Fin n, k < a → B a k = 0) (hB1 : ∀ a, B a a = 1)
    (hZ : ∀ a b, (A * W * B) a b ∈ I (k a + k b)) (hW : W.det ≠ 0)
    (hc : ∀ k b : Fin n, l ≤ (k : ℕ) → (b : ℕ) < l → W k b = 0)
    (hc' : ∀ k b : Fin n, l' ≤ (k : ℕ) → (b : ℕ) < l' → W k b = 0)
    (hAO : ∀ a b : Fin n, (a : ℕ) < l → l' ≤ (b : ℕ) → a ≠ b → A a b = 0)
    (t : K) (ε : Fin n → K) (hε : ∀ b, ε b ∈ I 0) (hε2 : ∀ b, ε b * ε b = 1)
    (hcol : ∀ a b : Fin n, l' ≤ (b : ℕ) → (b : ℕ) < l →
      W a b = (if (a : ℕ) + b + 1 = l + l' then t else 0) * ε b)
    (hrow : ∀ a b : Fin n, l' ≤ (a : ℕ) → (a : ℕ) < l →
      W a b = (if (a : ℕ) + b + 1 = l + l' then t else 0) * ε b)
    (i : Fin n) (hi' : l' ≤ (i : ℕ)) (hi : (i : ℕ) < l) (j : Fin n) :
    (W.submatrix (Fin.castLE h) (Fin.castLE h)).det * A j i ∈
        I (2 * ∑ a : Fin l, k (Fin.castLE h a) + (k j - k i)) ∧
      (W.submatrix (Fin.castLE h) (Fin.castLE h)).det * (W.submatrix (Fin.castLE h') (Fin.castLE h')).det *
        B i j ∈ I (2 * ∑ a : Fin l, k (Fin.castLE h a) + 2 * ∑ a : Fin l', k (Fin.castLE h' a) +
          (k j - k i)) := by sorry
