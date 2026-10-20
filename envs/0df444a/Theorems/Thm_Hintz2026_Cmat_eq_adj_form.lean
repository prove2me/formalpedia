-- Prove2me | Theorems.Thm_Hintz2026_Cmat_eq_adj_form
-- name    : Hintz2026.Cmat_eq_adj_form
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T14:53:16.549308+00:00
-- url     : https://prove2.me/theorems/28e1b375-060f-4889-b026-bd4e5b922bde
-- title:
--   Adjugate form of $C$: $C = (Q^2-M^2)^{-1}\,\operatorname{adj}(X)(cI-B)\operatorname{adj}(X)^*$
-- statement:
--   On $U$ the coupling matrix of Hintz eq. (7) can be written without inverses:
--
--   $$C^{(\varsigma)} = \frac{1}{Q^2-M^2}\;\operatorname{adj}(X)\,\bigl(c^{(\varsigma)}I - B^{(\varsigma)}\bigr)\,\operatorname{adj}(X)^*,$$
--
--   using $\det X = Q^2 - M^2$ (a nonzero real constant), $\det X^* = \overline{\det X} = \det X$, and $(X^*)^{-1} = (\det X)^{-1}\operatorname{adj}(X^*) = (\det X)^{-1}\operatorname{adj}(X)^*$. This form is the starting point of the explicit entry computation of $C$.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eq. (7)/(8) and the text after (7); local source Atlas/Perturbations/Hintz2026/CAdjugate.lean at commit 8d059e0 (no public Git remote)

import Definitions.Def_Hintz2026_System4
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.Cmat_eq_adj_form (p : SubextremalKN) (sg om mm : ℝ) {x : Fin 2 -> ℝ} (hx : x ∈ U p) : Cmat p sg om mm x = (((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ))⁻¹ • (adjugate (X p x) * (cscalar p sg om mm x • 1 - Bmat p sg om mm x) * (adjugate (X p x))ᴴ) := by sorry
