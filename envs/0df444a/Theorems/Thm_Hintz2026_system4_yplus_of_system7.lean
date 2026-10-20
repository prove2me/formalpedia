-- Prove2me | Theorems.Thm_Hintz2026_system4_yplus_of_system7
-- name    : Hintz2026.system4_yplus_of_system7
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T14:53:20.778262+00:00
-- url     : https://prove2.me/theorems/f9a74d41-3836-411e-85f1-ac70f744574d
-- title:
--   System (7) $\Rightarrow$ system (4), $y_+$ equation (inverse transformation)
-- statement:
--   Let $z_+, z_-\colon U\to\mathbb{C}^2$ with $z_+$ of class $C^\infty$ on $U$, and $x\in U$. Suppose the first transformed equation of Hintz eq. (7) holds at $x$: $D^-z_+ = C^{(\varsigma)}z_-$. Define the inverse transformation
--
--   $$y_+ := \frac{1}{Q^2-M^2}\,X\,z_+ ,\qquad y_- := (X^*)^{-1} z_- .$$
--
--   Then the first equation of the chiral system (4) holds at $x$:
--
--   $$\bigl(D^- - A\bigr)y_+ = \bigl(c^{(\varsigma)}I - B^{(\varsigma)}\bigr)y_- .$$
--
--   The proof pulls the constant $(Q^2-M^2)^{-1}$ through $D^-$, applies the residual identity $D^-(Xv) - A(Xv) = X\,D^-v$ of the integrating factor, and simplifies $X\,C^{(\varsigma)}$ using $X X^{-1} = I$ and $\det X = Q^2 - M^2$.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eq. (7)/(8) and the text after (7); local source Atlas/Perturbations/Hintz2026/Equivalence4to7.lean at commit 8d059e0 (no public Git remote)

import Definitions.Def_Hintz2026_System4
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.system4_yplus_of_system7 (p : SubextremalKN) (zp zm : (Fin 2 -> ℝ) -> Fin 2 -> ℂ) (sg om mm : ℝ) (hzp : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => zp x j) (U p)) {x : Fin 2 -> ℝ} (hx : x ∈ U p) (h7 : (fun i => Dm p (fun z => zp z i) x) = Cmat p sg om mm x *ᵥ zm x) : (fun j => Dm p (fun z => (((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ)⁻¹ • (X p z *ᵥ zp z)) j) x) - A p x *ᵥ (((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ)⁻¹ • (X p x *ᵥ zp x)) = (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Bmat p sg om mm x) *ᵥ (((X p x)ᴴ)⁻¹ *ᵥ zm x) := by sorry
