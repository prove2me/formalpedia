-- Prove2me | Theorems.Thm_GlobalTheory_SmithBetween_smith_between
-- name    : GlobalTheory.SmithBetween.smith_between
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:28.1818+00:00
-- url     : https://prove2.me/theorems/33abf9ff-0e28-49b2-8f03-8d9e00a7e5ba
-- title:
--   Smith Between: smith between
-- statement:
--   The Smith Between construction uses the smith between property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsMulEqMulDiagonal.lean#L52-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsMulEqMulDiagonal.lean#L52-L162

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsMulEqMulDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField
open GlobalTheory GlobalTheory.SmithBetween
open Matrix
open IsDedekindDomain NumberField
open Matrix

theorem GlobalTheory.SmithBetween.smith_between (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R)
    (hϖ : Irreducible ϖ) (n k : ℕ) (hk : k ≤ n) (M M' : Matrix (Fin n) (Fin n) R)
    (hMM : M * M' = ϖ • (1 : Matrix (Fin n) (Fin n) R)) (hdet : Associated M.det (ϖ ^ k)) :
    ∃ P Q : Matrix (Fin n) (Fin n) R, IsUnit P.det ∧ IsUnit Q.det ∧
      M * Q = P * Matrix.diagonal (fun i : Fin n => if i.1 < n - k then (1 : R) else ϖ) := by sorry
