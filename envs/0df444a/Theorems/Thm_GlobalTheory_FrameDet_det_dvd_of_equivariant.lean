-- Prove2me | Theorems.Thm_GlobalTheory_FrameDet_det_dvd_of_equivariant
-- name    : GlobalTheory.FrameDet.det_dvd_of_equivariant
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:03:46.274519+00:00
-- url     : https://prove2.me/theorems/7b427a61-2dd3-454d-a67b-84ef5ad3ef80
-- title:
--   Frame Det: det dvd of equivariant
-- statement:
--   The Frame Det construction uses the det dvd of equivariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/DetDvdEquivariantFramePolynomial.lean#L29-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/DetDvdEquivariantFramePolynomial.lean#L29-L111

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsHomogeneousOfEquivariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_DetDvdEquivariantFramePolynomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MvPolynomial Formalism.L2.LamCM
open GlobalTheory GlobalTheory.FrameDet
open GlobalTheory.BorelAlg

theorem GlobalTheory.FrameDet.det_dvd_of_equivariant : ∀ (K : Type) [Field K] [Infinite K] (B : Type) [Fintype B] [DecidableEq B] (m : B → ℕ) (P : MvPolynomial (FrVar m) K) (a : ∀ b, Fin (m b) → ℕ), (∀ (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K) (b : B) (t : Matrix (Fin (m b)) (Fin (m b)) K), (∀ b', (X b').det ≠ 0) → t.det ≠ 0 → t.BlockTriangular id → evalFr P (Function.update X b (X b * t)) = (∏ i, t i i ^ (a b i)) * evalFr P X) → ∀ b : B, (∀ i, 1 ≤ a b i) → ∃ Q : MvPolynomial (FrVar m) K, P = (Matrix.of fun i k : Fin (m b) => (MvPolynomial.X ⟨b, (k, i)⟩ : MvPolynomial (FrVar m) K)).det * Q := by sorry
