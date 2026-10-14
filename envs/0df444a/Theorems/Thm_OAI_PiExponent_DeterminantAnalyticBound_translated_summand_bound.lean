-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantAnalyticBound_translated_summand_bound
-- name    : OAI.PiExponent.DeterminantAnalyticBound.translated_summand_bound
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-11T19:20:18.176374+00:00
-- url     : https://prove2.me/theorems/4340823c-de0b-446e-9161-c7ddd0bcb17a
-- title:
--   Exponential bound for a translated scalar–determinant summand
-- statement:
--   Let finite index types $\iota,\kappa$, a grouping $g:\iota\to\kappa$, nonnegative group weights $w$, and complex numbers $s,d$ satisfy the original scalar and determinant exponential bounds. Assume $H,N>0$, $A,\eta,\nu,c\ge0$, total weight at least $|\iota|H\bar b$, and at most $N$ groups of weight at most $AH$. Then
--
--   $$\|sd\|\le \exp\!\left(|\iota|H\left[E_{\mathrm{tr}}+E_{\mathrm{hol}}+\rho+\max\!\left\{-\frac{c\eta^2|\iota|}{HN},-\nu(A(1-\eta)-\bar b)\right\}\right]\right).$$
--
--   The determinant hypothesis contains the collision occupancy sum $\sum_{a\in\kappa}m(g,a)^2$, where $m(g,a)=\#\{i:g(i)=a\}$. The scalar hypothesis contains $-\nu(\sum_i w(g(i))-|\iota|H\bar b)+|\iota|HE_{\mathrm{tr}}$, and the determinant hypothesis contains $-c\sum_a m(g,a)^2+|\iota|H(E_{\mathrm{hol}}+\rho)$. No sign assumption on $E_{\mathrm{tr}},E_{\mathrm{hol}},\rho,\bar b$ is added.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean#L80-L103

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_CollisionCombinatorics_Multiplicity

open scoped BigOperators

open OAI.PiExponent

theorem OAI.PiExponent.DeterminantAnalyticBound.translated_summand_bound
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (weight : κ → ℝ) (scalar determinant : ℂ)
    {H A eta nu c N bbar Etr Ehol rho : ℝ}
    (hH : 0 < H) (hA : 0 ≤ A) (heta : 0 ≤ eta) (hnu : 0 ≤ nu)
    (hc : 0 ≤ c) (hN : 0 < N) (hw : ∀ a, 0 ≤ weight a)
    (hbeta : (Fintype.card ι : ℝ) * H * bbar ≤ ∑ i, weight (group i))
    (hcap : (((Finset.univ : Finset κ).filter (fun a => weight a ≤ A * H)).card : ℝ) ≤ N)
    (hscalar : ‖scalar‖ ≤ Real.exp
      (-nu * ((∑ i, weight (group i)) - (Fintype.card ι : ℝ) * H * bbar) +
        (Fintype.card ι : ℝ) * H * Etr))
    (hdet : ‖determinant‖ ≤ Real.exp
      (-c * (∑ a, (Collision.multiplicity Finset.univ group a : ℝ) ^ 2) +
        (Fintype.card ι : ℝ) * H * (Ehol + rho))) :
    ‖scalar * determinant‖ ≤ Real.exp ((Fintype.card ι : ℝ) * H *
      (Etr + Ehol + rho + max (-c * eta ^ 2 * (Fintype.card ι : ℝ) / (H * N))
        (-nu * (A * (1 - eta) - bbar)))) := by
  sorry
