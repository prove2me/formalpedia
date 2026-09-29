-- Prove2me | Theorems.Thm_Mandelbrot_exists_iterate_zero_eq_of_mem_frontier
-- name    : Mandelbrot.exists_iterate_zero_eq_of_mem_frontier
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T13:27:22.756199+00:00
-- url     : https://prove2.me/theorems/b287ec6f-8a45-4e07-be46-a134afdec2fa
-- title:
--   Near $c_0 \in \partial M$ the critical orbit hits any analytically moving point
-- statement:
--   Let $M$ be the Mandelbrot set, $f_c(z) = z^2 + c$, and $c_0 \in \partial M$. Let $a$ be a holomorphic function on a neighbourhood of $c_0$. Then every neighbourhood $V$ of $c_0$ contains a parameter $c$ such that the critical orbit of $f_c$ passes through $a(c)$:
--
--   $$\exists\, c \in V,\ \exists\, N \ge 0 : \quad f_c^{N}(0) = a(c).$$
--
--   This expresses the instability of the critical orbit at boundary parameters: since the family $c \mapsto f_c^{N}(0)$ is not normal at any point of $\partial M$, it cannot avoid an analytically moving point (together with its analytically moving preimages) near $c_0$. In Shishikura's proof of Theorem 1 it is applied to a point $a(c) = \iota_c(z_0)$ of a holomorphically moving hyperbolic set.
--
--   **Formalization Note** The source cites Mañé–Sad–Sullivan (Lemma III.2 of *On the dynamics of rational maps*, Ann. Sci. ENS 1983) for this step, in the form "there exist $\lambda_1$ near $\lambda_0$, an integer $N > 0$ and a critical point $c$ with $f^N_{\lambda_1}(c) = i_{\lambda_1}(z_0)$"; for the quadratic family the only finite critical point is $0$. The statement here allows $N = 0$ and $c = c_0$.
-- source:
--   M. Shishikura, The Hausdorff dimension of the boundary of the Mandelbrot set and Julia sets, Ann. of Math. (2) 147 (1998), 225-267, https://arxiv.org/abs/math/9201282, §3, proof of Theorem 1 (the step citing Mañé-Sad-Sullivan, Lemma III.2)

import Definitions.Def_mandelbrot_hyperbolic_sets
open Topology Set Function Filter Bornology Metric MeasureTheory

namespace Mandelbrot

/-- **Mañé–Sad–Sullivan** (as used in the proof of Theorem 1 of Shishikura 1998): if
`c₀ ∈ ∂M` and `a` is holomorphic near `c₀`, then every neighbourhood of `c₀` contains a parameter
`c` for which some iterate of the critical point `0` under `z ↦ z ^ 2 + c` equals `a c`. -/
theorem exists_iterate_zero_eq_of_mem_frontier (c₀ : ℂ) (hc₀ : c₀ ∈ frontier mandelbrotSet)
    (a : ℂ → ℂ) (ha : AnalyticAt ℂ a c₀) (V : Set ℂ) (hV : V ∈ 𝓝 c₀) :
    ∃ c ∈ V, ∃ N : ℕ, (fun z ↦ z ^ 2 + c)^[N] 0 = a c := by sorry

end Mandelbrot
