-- Prove2me | Theorems.Thm_OffloadGNEP_Mono_hasFDerivAt_F_eq_JF
-- name    : OffloadGNEP.Mono.hasFDerivAt_F_eq_JF
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:46:33.605072+00:00
-- url     : https://prove2.me/theorems/6a93a116-87f9-49e7-85d6-a414f52d5356
-- title:
--   (16)–(17), p. 12 — the Jacobian of the offloading VI map F
-- statement:
--   Assume Assumption A and the standing hypotheses ($n\ge1$, $0<\chi\le1$). Let $x\in\mathbb R^{3N}$ satisfy $\alpha_ux_{u,m}<1$ for every user $u$ and $\frac1n\sum_t\delta_tx_{t,clet}<1$. Then the VI map $F$ is Fréchet differentiable at $x$, and its derivative is the matrix $JF(x)$ of (16)–(17):
--   $$F'(x)h\,\big|_{(u,i)}=\sum_{v}\sum_{j\in I}JF(x)_{(u,i),(v,j)}\,h_{v,j},$$
--   where $JF(x)$ has $A_u=\frac{2\alpha_u^2}{(1-\alpha_ux_{u,m})^3}$ at $((u,m),(u,m))$, $B_u=\frac2n\delta_u^2\frac{1-\frac1n\sum_{v\ne u}\delta_vx_{v,clet}}{(1-\frac1n\sum_t\delta_tx_{t,clet})^3}$ at $((u,clet),(u,clet))$, $B_{uv}=\frac1n\delta_v\delta_u\frac{1-\frac1n\sum_t\delta_tx_{t,clet}+\frac2n\delta_ux_{u,clet}}{(1-\frac1n\sum_t\delta_tx_{t,clet})^3}$ at $((u,clet),(v,clet))$ for $v\ne u$, and zeros elsewhere.
--
--   The open region described by the two strict inequalities contains $K$ under Assumption A, so this identifies the Jacobian on which the monotonicity analysis of Theorem 1 rests.
--
--   **Formalization Note** The derivative is asserted to exist as a continuous linear map whose action is given entrywise by the matrix `JF`. The region of differentiability is stated explicitly because $F$ has the denominators $1-\alpha_ux_{u,m}$ and $D$.
-- source:
--   Cardellini et al., A game-theoretic approach to computation offloading in mobile cloud computing, accepted manuscript (IRIS Sapienza 11573/779661; DOI 10.1007/s10107-015-0881-6), p. 12, (16)–(17)

import Mathlib
import Definitions.Def_OffloadGNEP_Mono_Setting

namespace OffloadGNEP.Mono

theorem hasFDerivAt_F_eq_JF {N : ℕ} (P : Params N) (hA : P.AssumptionA) (hS : P.Standing)
    (x : Fin N → Tier → ℝ) (hm : ∀ u, P.alpha u * x u .m < 1) (hload : load P x < 1) :
    ∃ L : (Fin N → Tier → ℝ) →L[ℝ] (Fin N → Tier → ℝ), HasFDerivAt (F P) L x ∧
      ∀ (h : Fin N → Tier → ℝ) (u : Fin N) (i : Tier),
        L h u i = ∑ v, ∑ j, JF P x (u, i) (v, j) * h v j := by sorry

end OffloadGNEP.Mono
