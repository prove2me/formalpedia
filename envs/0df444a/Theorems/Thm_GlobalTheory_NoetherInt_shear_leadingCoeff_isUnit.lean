-- Prove2me | Theorems.Thm_GlobalTheory_NoetherInt_shear_leadingCoeff_isUnit
-- name    : GlobalTheory.NoetherInt.shear_leadingCoeff_isUnit
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:34:32.605493+00:00
-- url     : https://prove2.me/theorems/ae6310d2-8b39-4cad-908e-b38fb299955d
-- title:
--   Noether Int: shear leading Coeff is Unit
-- statement:
--   The Noether Int construction uses the shear leading Coeff is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsQuasiFinitePolynomialMap.lean#L198-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsQuasiFinitePolynomialMap.lean#L198-L223

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsQuasiFinitePolynomialMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NoetherInt
open MvPolynomial
variable {k : Type*} [Field k] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) k)
variable (v w : Fin (n + 1) →₀ ℕ)
local notation3 "up" => 2 + f.totalDegree
local notation3 "r" => fun (i : Fin (n + 1)) ↦ up ^ i.1
local notation3 "T" => shear k n (2 + f.totalDegree)

theorem GlobalTheory.NoetherInt.shear_leadingCoeff_isUnit (fne : f ≠ 0) :
    IsUnit (finSuccEquiv k n (T f)).leadingCoeff := by sorry
