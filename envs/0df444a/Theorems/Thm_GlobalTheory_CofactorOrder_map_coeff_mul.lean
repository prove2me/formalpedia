-- Prove2me | Theorems.Thm_GlobalTheory_CofactorOrder_map_coeff_mul
-- name    : GlobalTheory.CofactorOrder.map_coeff_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:14:44.874902+00:00
-- url     : https://prove2.me/theorems/d00629fb-a9cd-4145-bff1-b1a98bc5db8a
-- title:
--   Cofactor Order: map coeff mul
-- statement:
--   The Cofactor Order construction uses the map coeff mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsNotXPowDvdAdjugateOfFirstOrderKernel.lean#L96-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsNotXPowDvdAdjugateOfFirstOrderKernel.lean#L96-L100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsNotXPowDvdAdjugateOfFirstOrderKernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open GlobalTheory
open GlobalTheory.CofactorOrder
variable {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]

theorem GlobalTheory.CofactorOrder.map_coeff_mul (P Q : Matrix n n K) (Ψ : Matrix n n K[X]) (k : ℕ) :
    ((P.map C * Ψ * Q.map C).map fun p => p.coeff k) = P * (Ψ.map fun p => p.coeff k) * Q := by sorry
