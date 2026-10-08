-- Prove2me | Theorems.Thm_NelderMeadLD_Rate1D_lemma_4_6
-- name    : NelderMeadLD.Rate1D.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:13:09.998551+00:00
-- url     : https://prove2.me/theorems/e3283682-87f3-41f1-879f-db43510a6aa6
-- title:
--   Lemma 4.6, p. 131 — with ρ = 1: at most r* = ⌈χ − 1⌉ consecutive reflections, and no expansion right after a reflection
-- statement:
--   Let $f:\mathbb R \to \mathbb R$ be strictly convex with bounded level sets, and apply the one-dimensional Nelder–Mead method with reflection coefficient $\rho = 1$, expansion coefficient $\chi > 1$, contraction coefficient $0 < \gamma < 1$ and shrink coefficient $0 < \sigma < 1$, starting from a nondegenerate ordered initial interval $\Delta_0$. Let
--   $$r^* = \lceil \chi - 1 \rceil.$$
--   Then:
--   1. the number of consecutive reflections is at most $r^*$: there is no $k$ such that iterations $k, k+1, \dots, k + r^*$ are all reflections;
--   2. the iteration immediately following a reflection is never an expansion.
--
--   These two facts restrict which move sequences the method can produce in dimension 1 with $\rho = 1$, and are the first ingredients of the paper's M-step linear convergence result (Theorem 4.2).
--
--   **Formalization Note.** $\rho = 1$ is substituted into the algorithm. The standing conditions (2.1) are carried as a hypothesis; with $\rho = 1$ they reduce to $\chi > 1$, $0 < \gamma < 1$, $0 < \sigma < 1$. $r^*$ is the natural-number ceiling `⌈χ − 1⌉₊`, equal to the paper's value for $\chi > 1$.
-- source:
--   Lagarias, Reeds, Wright & Wright, Convergence properties of the Nelder–Mead simplex method in low dimensions, SIAM J. Optim. 9 (1998), p. 131, Lemma 4.6

import Mathlib
import Definitions.Def_NelderMeadLD_Conv1D_Algorithm
import Definitions.Def_NelderMeadLD_Rate1D_Algorithm

namespace NelderMeadLD.Rate1D

open NelderMeadLD.Conv1D

theorem lemma_4_6 (χ γ σ : ℝ) (hpar : ParamsOK 1 χ γ σ)
    (f : ℝ → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (hlev : ∀ μ : ℝ, Bornology.IsBounded {x | f x ≤ μ})
    (p0 : ℝ × ℝ) (h0 : IsStart f p0) :
    (∀ k : ℕ, ¬ ∀ i < rStar χ + 1, moveAt f χ γ σ p0 (k + i) = Move.reflect) ∧
    (∀ k : ℕ, moveAt f χ γ σ p0 k = Move.reflect →
      moveAt f χ γ σ p0 (k + 1) ≠ Move.expand) := by sorry

end NelderMeadLD.Rate1D
