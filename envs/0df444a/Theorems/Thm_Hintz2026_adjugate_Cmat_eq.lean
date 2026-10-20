-- Prove2me | Theorems.Thm_Hintz2026_adjugate_Cmat_eq
-- name    : Hintz2026.adjugate_Cmat_eq
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T14:53:22.507216+00:00
-- url     : https://prove2.me/theorems/eb70258e-9ea5-49bf-adf9-4aea6e5145bc
-- title:
--   Adjugate of $C$: $\operatorname{adj}C = (Q^2-M^2)^{-1}\,X^*(cI+B)\,X$
-- statement:
--   For $2\times 2$ matrices the adjugate is anti-multiplicative and $\operatorname{adj}(cI - B) = cI + B$ whenever $\operatorname{tr}B = 0$ (which holds for $B^{(\varsigma)}$ of Hintz eq. (4)). Combining this with the adjugate form of $C$ gives, on $U$,
--
--   $$\operatorname{adj}\bigl(C^{(\varsigma)}\bigr) = \frac{1}{Q^2-M^2}\;X^*\,\bigl(c^{(\varsigma)}I + B^{(\varsigma)}\bigr)\,X .$$
--
--   This is the matrix appearing on the right of the second transformed equation $D^+z_- = \operatorname{adj}(C)\,z_+$ of eq. (7).
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eq. (7)/(8) and the text after (7); local source Atlas/Perturbations/Hintz2026/CAdjugate.lean at commit 8d059e0 (no public Git remote)

import Definitions.Def_Hintz2026_System4
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.adjugate_Cmat_eq (p : SubextremalKN) (sg om mm : ℝ) {x : Fin 2 -> ℝ} (hx : x ∈ U p) : adjugate (Cmat p sg om mm x) = (((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ))⁻¹ • ((X p x)ᴴ * (cscalar p sg om mm x • 1 + Bmat p sg om mm x) * X p x) := by sorry
