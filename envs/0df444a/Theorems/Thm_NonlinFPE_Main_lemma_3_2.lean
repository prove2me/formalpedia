-- Prove2me | Theorems.Thm_NonlinFPE_Main_lemma_3_2
-- name    : NonlinFPE.Main.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:39.963608+00:00
-- url     : https://prove2.me/theorems/cec896e0-a0c8-46af-aef6-bd9cb08d8b2a
-- title:
--   Lemma 3.2, p. 11 — under (H1)–(H3) and (K), the Dirichlet problem (3.16) on B_N has a solution u_N ∈ H¹₀(B_N) with the N- and λ-uniform bound (3.17)
-- statement:
--   Assume (H1)–(H3) with ellipticity constant $\gamma > 0$ and the additional hypotheses (K), (3.15). Write $a^*_{ij}(x,u) = a_{ij}(x,u)u$, $b^*(x,u) = b(x,u)u$ and $B_N = \{\xi \in \mathbb R^d : |\xi| < N\}$.
--
--   There is $\lambda_0 > 0$ such that for every $f \in L^2(\mathbb R^d)$ there is a constant $C$ with the following property: for every $N > 0$ and every $\lambda \in (0,\lambda_0)$ there is a solution $u_N \in H^1_0(B_N)$ of
--   $$u - \lambda\sum_{i,j=1}^d D^2_{ij}\big(a^*_{ij}(u)\big) + \lambda\operatorname{div}\big(b^*(x,u)\big) = f \ \text{ in } B_N, \qquad u = 0 \text{ on } \partial B_N, \tag{3.16}$$
--   satisfying
--   $$\|u_N\|^2_{L^2(B_N)} + \lambda\gamma\|\nabla u_N\|^2_{L^2(B_N)} \le C\|f\|^2_{L^2(B_N)}. \tag{3.17}$$
--   So $C$ does not depend on $N$ or $\lambda$.
--
--   This is the first approximation step of Proposition 3.1: solutions on balls, with bounds uniform in the radius, which Lemma 3.3 passes to the limit $N \to \infty$.
--
--   **Formalization Note** The page fixes $\lambda_0 = \gamma(b_\infty^2 + c_\infty^2)^{-1}$; the statement asserts only *some* $\lambda_0 > 0$ (a disclosed weakening: the printed estimate (3.19) omits dimension factors, and only the existence of some $\lambda_0$ is used afterwards). (3.16) is taken in $\mathcal D'(B_N)$ in the derivative-free weak form of the mission's `ResolventEqOn` (test functions supported in $B_N$). $u_N \in H^1_0(B_N)$ is encoded as: $u_N$ vanishes a.e. outside $B_N$ and lies in $H^1(\mathbb R^d)$ with weak gradient $g$ (for the ball, a Lipschitz domain, this is equivalent to the closure definition of $H^1_0$); $\|\nabla u_N\|^2_{L^2(B_N)} = \int_{B_N}\sum_i g_i^2$.
-- source:
--   Barbu, Röckner, From nonlinear Fokker-Planck equations to solutions of distribution dependent SDE, arXiv:1808.10706v4, Lemma 3.2, p. 11, (3.16)–(3.17); hypotheses (K), (3.15), p. 10

import Mathlib
import Definitions.Def_NonlinFPE_Main_Setting
import Definitions.Def_NonlinFPE_Main_MAccretive

open MeasureTheory
open scoped NNReal

namespace NonlinFPE.Main

open EthierKurtz

/-- Lemma 3.2, p. 11, under (H1)–(H3) and (K): for some `λ₀ > 0` and every `f ∈ L²` there is `C`
such that for every `N > 0` and `λ ∈ (0, λ₀)` the Dirichlet problem (3.16) on the ball `B_N` has a
solution `u_N ∈ H¹₀(B_N)` with `‖u_N‖² + λγ‖∇u_N‖² ≤ C‖f‖²` on `B_N`. -/
theorem lemma_3_2 {d : ℕ} (a : Fin d → Fin d → SDEState d → ℝ → ℝ)
    (b : Fin d → SDEState d → ℝ → ℝ) (γ : ℝ) (hND : HypND a b γ) (hK : HypK a b) :
    ∃ lam0 : ℝ, 0 < lam0 ∧
      ∀ f : SDEState d → ℝ, MemLp f 2 volume →
        ∃ C : ℝ, ∀ N : ℝ, 0 < N → ∀ lam : ℝ, 0 < lam → lam < lam0 →
          ∃ (uN : SDEState d → ℝ) (g : Fin d → SDEState d → ℝ),
            IsH1 uN g ∧
            (∀ᵐ x ∂(volume : Measure (SDEState d)), x ∉ Metric.ball (0 : SDEState d) N → uN x = 0) ∧
            ResolventEqOn (Metric.ball (0 : SDEState d) N) a b lam uN f ∧
            (∫ x in Metric.ball (0 : SDEState d) N, uN x ^ 2) +
                lam * γ * ∫ x in Metric.ball (0 : SDEState d) N, ∑ i, g i x ^ 2 ≤
              C * ∫ x in Metric.ball (0 : SDEState d) N, f x ^ 2 := by sorry

end NonlinFPE.Main
