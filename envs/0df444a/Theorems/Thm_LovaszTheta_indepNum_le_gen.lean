-- Prove2me | Theorems.Thm_LovaszTheta_indepNum_le_gen
-- name    : LovaszTheta.indepNum_le_gen
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T14:37:28.653288+00:00
-- url     : https://prove2.me/theorems/c296eb53-4503-46d1-80cb-6535d7dedae2
-- title:
--   Lovasz Theta: indep Num le gen
-- statement:
--   Lovász's bound for vectors indexed by an arbitrary finite type.
--
--   Source: https://github.com/jtraverso/lovasz-theta/blob/2d506b5abca378d9133b5e3f1264a5316843c9a7/ThetaLib/Theta.lean#L81-L98
-- source:
--   https://github.com/jtraverso/lovasz-theta/blob/2d506b5abca378d9133b5e3f1264a5316843c9a7/ThetaLib/Theta.lean#L81-L98

module
public import Mathlib
public import Definitions.Def_ThetaLib_Theta
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open LovaszTheta
variable {V : Type*}

theorem LovaszTheta.indepNum_le_gen [Finite V] (G : SimpleGraph V) {ι : Type*} [Fintype ι]
    (u : V → ι → ℝ)
    (hu1 : ∀ i, dotProduct (u i) (u i) = 1)
    (hu0 : ∀ i j, i ≠ j → ¬ G.Adj i j → dotProduct (u i) (u j) = 0)
    {c : ι → ℝ} (hc : dotProduct c c = 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : ∀ i, 1 ≤ t * dotProduct c (u i) ^ 2) :
    (G.indepNum : ℝ) ≤ t := by sorry
