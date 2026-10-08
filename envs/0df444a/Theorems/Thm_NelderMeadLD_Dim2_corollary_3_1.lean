-- Prove2me | Theorems.Thm_NelderMeadLD_Dim2_corollary_3_1
-- name    : NelderMeadLD.Dim2.corollary_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:14:41.387499+00:00
-- url     : https://prove2.me/theorems/100a0142-db9c-43cb-b200-3166fcad4bf3
-- title:
--   Corollary 3.1, p. 122 — if the best vertex changes infinitely often, all limiting vertex values coincide
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ ($n\ge1$) be bounded below, let the coefficients satisfy (2.1), and let $(\Delta_k)$ be a run of Algorithm NM on $f$ from a nondegenerate initial simplex in which no shrink step occurs. If the best vertex changes infinitely often, i.e. $x_1^{(k+1)}\ne x_1^{(k)}$ for infinitely many $k$, then there is a single number $L$ with
--   $$\lim_{k\to\infty} f_i^{(k)}=L\qquad\text{for every } i=1,\dots,n+1,$$
--   that is, $f_1^*=\dots=f_{n+1}^*$.
--
--   This corollary of broken convergence settles the case of Theorem 5.1 in which the best vertex keeps moving.
--
--   **Formalization Note** "The change index is 1 infinitely often" is written as: for every $N$ there is $k\ge N$ with $x_1^{(k+1)}\ne x_1^{(k)}$ (index `0` in Lean). The conclusion asserts the existence of the common limit.
-- source:
--   Lagarias, Reeds, Wright & Wright, Convergence properties of the Nelder–Mead simplex method in low dimensions, SIAM J. Optim. 9 (1998), p. 122, Corollary 3.1

import Mathlib
import Definitions.Def_NelderMeadLD_Dim2_Algorithm
open Filter Topology

namespace NelderMeadLD.Dim2

theorem corollary_3_1 {n : ℕ} [NeZero n] (f : E n → ℝ) (ρ χ γ σ : ℝ) (hpar : NelderMeadLD.Conv1D.ParamsOK ρ χ γ σ)
    (Δ : ℕ → Fin (n + 1) → E n) (hrun : IsNMRun f ρ χ γ σ Δ) (hnd : Nondegenerate (Δ 0))
    (hbdd : BddBelow (Set.range f)) (hnoshrink : ∀ k, ¬ IsShrinkAt f ρ χ γ Δ k)
    (hinf : ∀ N : ℕ, ∃ k ≥ N, Δ (k + 1) 0 ≠ Δ k 0) :
    ∃ L : ℝ, ∀ i, Tendsto (fun k => f (Δ k i)) atTop (𝓝 L) := by sorry

end NelderMeadLD.Dim2
