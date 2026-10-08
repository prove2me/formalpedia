-- Prove2me | Theorems.Thm_NestedLogitVariants_General_frac_prefix_optimum
-- name    : NestedLogitVariants.General.frac_prefix_optimum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:42:39.321578+00:00
-- url     : https://prove2.me/theorems/1e33f895-cb48-4e56-8255-4f60558c771b
-- title:
--   A.4 Case 1, p. 47 — the relaxed nest problem has an optimal solution of fractional-prefix form
-- statement:
--   Fix a nest $i$ with $\gamma_i>1$ of an instance satisfying the standing assumptions with at least one product, and any real $x$. Consider the relaxed nest problem
--   $$
--   \max_{z_i\in[0,1]^n}\ \Big(v_{i0}+\sum_{j\in N}v_{ij}z_{ij}\Big)^{\gamma_i}\left[\frac{\sum_{j\in N}r_{ij}v_{ij}z_{ij}}{v_{i0}+\sum_{j\in N}v_{ij}z_{ij}}-x\right].
--   $$
--   It has an optimal solution $\hat z_i$ of the form
--   $$
--   \hat z_{i1}=\dots=\hat z_{i,k-1}=1,\quad \hat z_{ik}\in[0,1],\quad \hat z_{i,k+1}=\dots=\hat z_{in}=0
--   $$
--   for some $k\in\{1,\dots,n\}$.
--
--   In Case 1 of the proof of Theorem 11 the problem is solved at $x=\beta\hat x$, and the fractional-prefix form of its solution is what makes inequality (30) applicable.
--
--   **Formalization Note** The page states this at $x=\beta\hat x$ for a nest with $\gamma_i>1$; it is stated here for a nest with $\gamma_i>1$ and every real $x$ (the value $\hat x$ is arbitrary). The existence of a maximizer is part of the claim. When $v_{i0}=0$ the objective at $z=0$ is $0$ in Lean, which is its limit as $z\to0$.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 47, Appendix A.4, Case 1

import Mathlib
import Definitions.Def_NestedLogitVariants_General_Model
import Definitions.Def_NestedLogitVariants_General_Relaxation

namespace NestedLogitVariants.General

/-- Appendix A.4, Case 1 (p. 47): in a nest with `γ_i > 1`, for every `x` (the page has
`x = β x̂`), the maximization of `F I i · x` over the box `[0, 1]^n` has an optimal solution of the form `z_1 = ⋯ = z_{k−1} = 1`, `z_k ∈ [0, 1]`,
`z_{k+1} = ⋯ = z_n = 0`. -/
theorem frac_prefix_optimum {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing)
    (hn : 0 < n) (i : ι) (hγi : 1 < I.γ i) (x : ℝ) :
    ∃ z ∈ box n, (∀ z' ∈ box n, F I i z' x ≤ F I i z x) ∧ ∃ k : Fin n, IsFracPrefix z k := by sorry

end NestedLogitVariants.General
