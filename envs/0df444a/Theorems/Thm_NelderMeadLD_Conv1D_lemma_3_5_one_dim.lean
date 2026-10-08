-- Prove2me | Theorems.Thm_NelderMeadLD_Conv1D_lemma_3_5_one_dim
-- name    : NelderMeadLD.Conv1D.lemma_3_5_one_dim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:20:51.225477+00:00
-- url     : https://prove2.me/theorems/d8d5a795-a0a7-4aa6-bfc0-353039b1726a
-- title:
--   Lemma 3.5 (case n = 1), p. 122 — for strictly convex f no shrink step is taken by the 1-D Nelder–Mead method
-- statement:
--   Let $f : \mathbb R \to \mathbb R$ be strictly convex, let the parameters satisfy (2.1), and run Algorithm NM in dimension $1$ from a nondegenerate initial interval $\Delta_0 = (x_1^{(0)}, x_2^{(0)})$, $x_1^{(0)} \ne x_2^{(0)}$, ordered so that $f(x_1^{(0)}) \le f(x_2^{(0)})$. Then for every iteration $k$,
--   $$\text{iteration } k \text{ is not a shrink step.}$$
--
--   This is the one-dimensional case of the paper's Lemma 3.5. It is why the shrink coefficient $\sigma$ plays no role in the one-dimensional analysis.
--
--   **Formalization Note** The general-$n$ Lemma 3.5 belongs to a separate mission of this series; this item is its $n = 1$ case on the one-dimensional algorithm of this mission. Bounded level sets are not needed and not assumed.
-- source:
--   Lagarias, Reeds, Wright & Wright, Convergence properties of the Nelder–Mead simplex method in low dimensions, SIAM J. Optim. 9 (1998), p. 122, Lemma 3.5 (case n = 1)

import Mathlib
import Definitions.Def_NelderMeadLD_Conv1D_Algorithm

open Filter Topology

namespace NelderMeadLD.Conv1D

theorem lemma_3_5_one_dim (f : ℝ → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (ρ χ γ σ : ℝ) (hpar : ParamsOK ρ χ γ σ)
    (p0 : ℝ × ℝ) (h0 : IsStart f p0) :
    ∀ k : ℕ, move f ρ χ γ (run f ρ χ γ σ p0 k) ≠ Move.shrink := by sorry

end NelderMeadLD.Conv1D
