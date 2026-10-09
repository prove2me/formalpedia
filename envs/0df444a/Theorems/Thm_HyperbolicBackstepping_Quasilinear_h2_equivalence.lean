-- Prove2me | Theorems.Thm_HyperbolicBackstepping_Quasilinear_h2_equivalence
-- name    : HyperbolicBackstepping.Quasilinear.h2_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:22:44.822087+00:00
-- url     : https://prove2.me/theorems/3069d742-9ae3-4d95-b2a8-93aa0bac88b9
-- title:
--   §5.1, p. 12 — the backstepping transformation γ = 𝒦[Φz] preserves the H² norm up to constants
-- statement:
--   Let the plant satisfy the standing assumptions of §2 with $q=G_0'(0)\neq0$, and let $K=(K^{uu},K^{uv};K^{vu},K^{vv})$ be a $C^2$ solution of the kernel equations (3.30)–(3.37) with the coefficients $\epsilon_i$, $c_i$ of (4.7), (4.9). For a profile $z_0:[0,1]\to\mathbb R^2$ let
--   $$\gamma_0(x)=\mathcal K[\Phi z_0](x)=\Phi(x)z_0(x)-\int_0^xK(x,\xi)\Phi(\xi)z_0(\xi)\,d\xi .$$
--   Then there is a constant $c>0$ such that for every $C^2$ profile $z_0$
--   $$\|\gamma_0\|_{H^2}\le c\,\|z_0\|_{H^2}\qquad\text{and}\qquad\|z_0\|_{H^2}\le c\,\|\gamma_0\|_{H^2}.$$
--
--   This equivalence lets the proof of Theorem 4.1 work with the backstepping variable $\gamma$ instead of $z$: an exponential $H^2$ estimate for $\gamma$ is one for $z$.
--
--   **Formalization Note** The page states the equivalence for the direct and inverse transformations (3.23), (3.38). Lean states it for the direct transformation only and makes the reverse inequality part of the claim, so no inverse kernel $L$ is assumed. Profiles are $C^2$ functions on $\mathbb R$ (classical version of $H^2$); $H^2$ norms are sums of $L^2$ norms of $z_0$, $z_0'$, $z_0''$ on $[0,1]$. The $C^2$ regularity of $K$ is a hypothesis (the paper's claim via Theorem A.2; it holds when $\Lambda$, $f$ are $C^3$).
-- source:
--   Coron, Vazquez, Krstic and Bastin, Local Exponential H² Stabilization of a 2 × 2 Quasilinear Hyperbolic System Using Backstepping, arXiv:1208.6475v1, p. 12, §5.1, paragraph after (5.18)

import Mathlib
import Definitions.Def_HyperbolicBackstepping_Quasilinear_ClosedLoop
import Definitions.Def_HyperbolicBackstepping_Quasilinear_Backstepping

namespace HyperbolicBackstepping.Quasilinear

theorem h2_equivalence (P : Plant) (hq : P.q ≠ 0)
    (Kuu Kuv Kvu Kvv : ℝ → ℝ → ℝ)
    (hK : IsFullKernel P.ε₁ P.ε₂ P.c₁ P.c₂ P.q Kuu Kuv Kvu Kvv) :
    ∃ c : ℝ, 0 < c ∧ ∀ z₀ : ℝ → Fin 2 → ℝ, ContDiff ℝ 2 z₀ →
      H2norm (transformK (Kmat Kuu Kuv Kvu Kvv) (scale P z₀)) ≤ c * H2norm z₀ ∧
      H2norm z₀ ≤ c * H2norm (transformK (Kmat Kuu Kuv Kvu Kvv) (scale P z₀)) := by sorry

end HyperbolicBackstepping.Quasilinear
