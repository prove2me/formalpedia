-- Prove2me | Theorems.Thm_GrothendieckTeichmuller_grt1_odd_degree_nonzero
-- name    : GrothendieckTeichmuller.grt1_odd_degree_nonzero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T21:47:53.846194+00:00
-- url     : https://prove2.me/theorems/9691ce44-b96b-49bf-97c9-195907c40cf4
-- title:
--   Corollary 5.2 — non-zero elements of $\mathfrak{grt}_1$ in every odd degree $\ge 3$
-- statement:
--   For every $p \ge 0$ there exists a non-zero $\psi \in \mathfrak{grt}_1$ that is homogeneous of degree $2p+3$.
--
--   Thus $\mathfrak{grt}_1$ contains non-zero elements in each of the degrees $3, 5, 7, \dots$, and in particular is infinite dimensional. In the source these elements are the components $\sigma_{2p+3}$ of the logarithm of the unique element of $GRT_1$ taking the Knizhnik-Zamolodchikov associator $\Phi_{KZ}(x,y)$ to $\Phi_{KZ}(-x,-y)$; their non-vanishing comes from the fact that the coefficients of $x^{j-1}y$ in these two associators differ in odd degrees $j \ge 3$, which in turn rests on the non-vanishing of $\zeta(j)$-type coefficients of $\Phi_{KZ}$.
--
--   The statement asks only for existence of such elements, not for the specific construction.
-- source:
--   Thomas Willwacher, The Grothendieck-Teichmüller Group, ETH Zürich lecture notes (in progress), 27 February 2014, Section 5.1, p. 49, Corollary 5.2

import Definitions.Def_GT_grt1

namespace GrothendieckTeichmuller

theorem grt1_odd_degree_nonzero (p : ℕ) :
    ∃ ψ : Lxy, ψ ∈ grt1 ∧ ψ ≠ 0 ∧ IsHomogeneousOfDegree (2 * p + 3) ψ := by sorry

end GrothendieckTeichmuller
