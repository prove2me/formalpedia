-- Prove2me | Theorems.Thm_GlobalTheory_det_saturated_lattice_baseChange
-- name    : GlobalTheory.det_saturated_lattice_baseChange
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:15:38.704904+00:00
-- url     : https://prove2.me/theorems/10234a51-192b-4053-b306-2bddbaaeb7df
-- title:
--   Global Theory: det saturated lattice base Change
-- statement:
--   The Global Theory construction uses the det saturated lattice base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralBasisChangeDeterminant.lean#L52-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralBasisChangeDeterminant.lean#L52-L154

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralBasisChangeDeterminant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix

theorem GlobalTheory.det_saturated_lattice_baseChange : ∀ (O k V K : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field k] [Algebra O k] [IsFractionRing O k] [CommRing V] [Field K] [Algebra V K] [IsFractionRing V K] (f : O →+* V) (em : k →+* K), (∀ a, algebraMap V K (f a) = em (algebraMap O k a)) → ∀ (m n : ℕ) (P : Matrix (Fin m) (Fin n) k) (M : Matrix (Fin m) (Fin m) k) (C : Matrix (Fin m) (Fin m) K), (∀ c, Matrix.vecMul c P = 0 → c = 0) → M.det ≠ 0 → (∀ c : Fin m → k, (∃ a : Fin n → O, Matrix.vecMul c P = fun j => algebraMap O k (a j)) ↔ ∃ b : Fin m → O, c = Matrix.vecMul (fun i => algebraMap O k (b i)) M) → (∀ c : Fin m → K, (∃ a : Fin n → V, Matrix.vecMul c (P.map em) = fun j => algebraMap V K (a j)) ↔ ∃ b : Fin m → V, c = Matrix.vecMul (fun i => algebraMap V K (b i)) C) → ∃ u : Vˣ, C.det = algebraMap V K u * em M.det := by sorry
