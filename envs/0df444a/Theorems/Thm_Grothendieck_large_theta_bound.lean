-- Prove2me | Theorems.Thm_Grothendieck_large_theta_bound
-- name    : Grothendieck.large_theta_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-02T04:20:14.356552+00:00
-- url     : https://prove2.me/theorems/00a7a8ce-e988-480a-ac77-266f9c4d4d65
-- title:
--   Theorem 5.1 — $K(r,G)=O(\log\vartheta(G)/r)$ for large theta number
-- statement:
--   There is a universal constant $C>0$ such that for every finite graph $G=(V,E)$ and every integer $r$ with
--
--   $$
--   1\le r\le\log\vartheta(G)
--   $$
--
--   one has
--
--   $$
--   K(r,G)\ \le\ C\cdot\frac{\log\vartheta(G)}{r}.
--   $$
--
--   This extends the Alon-Makarychev-Makarychev-Naor bound for rank $1$ — which gives $K(1,G)\le O(\log\vartheta(G))$ — to all ranks, and shows that for graphs of large theta number the linear dependence $\vartheta(G)-1$ of the main theorem can be replaced by a logarithmic one; the two bounds are complementary, the main theorem being better when $\vartheta(G)$ is small.
--
--   The proof is a different rounding scheme: instead of the Krivine-Haage­rup construction it uses the theta program's optimal solution to build two unit vector families $s,t$ in $\mathbb R^{2|V|+1}$ with $s(u)\cdot t(u)=1/\lambda$, $s(u)\cdot s(v)=t(u)\cdot t(v)=0$ across edges, and then rounds with a *truncated* Gaussian: $g_u(Z)=Zf(u)/R$ if $\lVert Zf(u)\rVert\le R$ and $Zf(u)/\lVert Zf(u)\rVert$ otherwise, with $Z$ having entries of variance $1/r$ and $R\ge2$ a parameter. Expanding $f(u)\cdot f(v)$ against the inner products of the auxiliary functions $h^0_u,h^1_u$ gives, after an incomplete-Gamma estimate for the truncation error, the explicit inequality
--
--   $$
--   \mathrm{SDP}_r(G,A)\ \ge\ \frac1{R^2}\Big(1-\Big(\frac12+\frac{\lambda\,2^{(r+1)/2}}{\sqrt r\,\Gamma(r/2)}\,\Gamma\big(\tfrac{r+1}2,\tfrac{rR^2}2\big)\Big)^2\Big)\,\mathrm{SDP}_\infty(G,A),
--   $$
--
--   and choosing $R^2=C'(\log\lambda)/r$ — which is where the hypothesis $r\le\log\lambda$ is used — makes the factor a positive constant.
--
--   **Formalization Note** The $O(\cdot)$ notation is spelled out as the existence of a single universal constant $C>0$ valid for all finite graphs and all $r$ with $1\le r\le\log\vartheta(G)$, both bounds being over the reals. Since the proof produces an explicit constant, the existential statement is not a weakening of the paper's claim.
-- source:
--   J. Briët, F. M. de Oliveira Filho, F. Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105, Theorem 5.1, p. 96, and its proof, pp. 96-98. https://doi.org/10.4086/toc.2014.v010a004

import Mathlib
import Definitions.Def_Grothendieck_Sdp
import Definitions.Def_Grothendieck_Theta

namespace Grothendieck

theorem large_theta_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (r : ℕ),
      1 ≤ r → (r : ℝ) ≤ Real.log (thetaComplement G) →
        grothendieckConstant r G ≤ C * (Real.log (thetaComplement G) / (r : ℝ)) := by sorry

end Grothendieck
