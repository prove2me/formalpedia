-- Prove2me | Theorems.Thm_Hintz2026_Cmat_mul_Xstar
-- name    : Hintz2026.Cmat_mul_Xstar
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T14:53:28.847807+00:00
-- url     : https://prove2.me/theorems/2470b305-a289-4896-9d03-30ef4b6a7e6f
-- title:
--   $C\,X^* = (\operatorname{adj}X)(cI - B)$
-- statement:
--   Let $C^{(\varsigma)} = (\det X)\,X^{-1}(c^{(\varsigma)}I - B^{(\varsigma)})(X^*)^{-1}$ be the coupling matrix of Hintz eq. (7), with $c^{(\varsigma)}$ and $B^{(\varsigma)}$ the scalar and matrix coefficients of eq. (4) (spin parameter $\varsigma\in\mathbb{R}$, the paper's two spin directions being $\varsigma=\pm 1$; frequency $\omega$ and azimuthal number $m$ real). Then at every point of $U$
--
--   $$C^{(\varsigma)}\,X^* = (\operatorname{adj}X)\,\bigl(c^{(\varsigma)}I - B^{(\varsigma)}\bigr).$$
--
--   This is the algebraic identity that turns $D^-z_+ = (\operatorname{adj}X)(cI-B)\,y_-$ into $D^-z_+ = C\,z_-$ with $z_- = X^*y_-$.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eq. (7)/(8) and the text after (7); local source Atlas/Perturbations/Hintz2026/Equivalence4to7.lean at commit 8d059e0 (no public Git remote)

import Definitions.Def_Hintz2026_System4
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.Cmat_mul_Xstar (p : SubextremalKN) (sg om mm : ℝ) {x : Fin 2 -> ℝ} (hx : x ∈ U p) : Cmat p sg om mm x * (X p x)ᴴ = adjugate (X p x) * (cscalar p sg om mm x • 1 - Bmat p sg om mm x) := by sorry
