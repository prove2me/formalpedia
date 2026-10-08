-- Prove2me | Theorems.Thm_NelderMeadLD_Dim2_lemma_3_6
-- name    : NelderMeadLD.Dim2.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:15:19.788988+00:00
-- url     : https://prove2.me/theorems/830a13dd-317a-4436-82af-6736f07f8b5a
-- title:
--   Lemma 3.6, p. 123 — strictly convex, bounded below, ργ < 1: f*ₙ = f*ₙ₊₁, and (n ≥ 2) xₙ changes infinitely often
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ ($n\ge1$) be strictly convex and bounded below, let the coefficients satisfy (2.1) and in addition
--   $$\rho\gamma<1,$$
--   and let $(\Delta_k)$ be a run of Algorithm NM on $f$ from a nondegenerate initial simplex. Then
--   1. the next-worst and worst vertex values have a common limit: $f_n^*=f_{n+1}^*$;
--   2. if $n\ge2$, there are infinitely many iterations $k$ with $x_n^{(k+1)}\ne x_n^{(k)}$.
--
--   The lemma is the input to Lemma 5.1, where it guarantees that the next-worst vertex of a triangle keeps moving.
--
--   **Formalization Note** $x_n$ is 0-based index $n-1$ (`nextWorst n`), $x_{n+1}$ is `Fin.last n`. Part 1 asserts the existence of a common limit $L$ of $f_n^{(k)}$ and $f_{n+1}^{(k)}$. The paper's statement does not name the start; its proof uses Lemma 3.4, which assumes a nondegenerate start, so that hypothesis is kept. Part 2 is restricted to $n\ge2$: for $n=1$ the next-worst vertex is the best vertex, and the printed claim is false (take $f(x)=x^2$, $\rho=1$, $\gamma=\tfrac12$, start $(0,1)$: every iteration is an accepted inside contraction and $x_1^{(k)}=0$ for all $k$); the proof's contradiction uses the strict inequality $f(\bar x)<f(x_n)$, which the paper notes holds only for $n>1$. The paper applies the lemma with $n=2$.
-- source:
--   Lagarias, Reeds, Wright & Wright, Convergence properties of the Nelder–Mead simplex method in low dimensions, SIAM J. Optim. 9 (1998), p. 123, Lemma 3.6

import Mathlib
import Definitions.Def_NelderMeadLD_Dim2_Algorithm
open Filter Topology

namespace NelderMeadLD.Dim2

theorem lemma_3_6 {n : ℕ} [NeZero n] (f : E n → ℝ) (ρ χ γ σ : ℝ) (hpar : NelderMeadLD.Conv1D.ParamsOK ρ χ γ σ)
    (Δ : ℕ → Fin (n + 1) → E n) (hrun : IsNMRun f ρ χ γ σ Δ) (hnd : Nondegenerate (Δ 0))
    (hf : StrictConvexOn ℝ Set.univ f) (hbdd : BddBelow (Set.range f)) (hργ : ρ * γ < 1) :
    (∃ L : ℝ, Tendsto (fun k => f (Δ k (nextWorst n))) atTop (𝓝 L) ∧
      Tendsto (fun k => f (Δ k (Fin.last n))) atTop (𝓝 L)) ∧
    (2 ≤ n → ∀ N : ℕ, ∃ k ≥ N, Δ (k + 1) (nextWorst n) ≠ Δ k (nextWorst n)) := by sorry

end NelderMeadLD.Dim2
