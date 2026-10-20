-- Prove2me | Theorems.Thm_Hintz2026_system4_yminus_of_system7
-- name    : Hintz2026.system4_yminus_of_system7
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T14:53:33.251956+00:00
-- url     : https://prove2.me/theorems/f28edaa5-816f-4edd-b4ba-051c11fcbbc2
-- title:
--   System (7) $\Rightarrow$ system (4), $y_-$ equation (inverse transformation)
-- statement:
--   Let $z_+, z_-\colon U\to\mathbb{C}^2$ with $z_-$ of class $C^\infty$ on $U$, and $x\in U$. Suppose the second transformed equation of Hintz eq. (7) holds at $x$: $D^+z_- = \operatorname{adj}(C^{(\varsigma)})\,z_+$. With the inverse transformation $y_- := (X^*)^{-1}z_-$ and $y_+ := (Q^2-M^2)^{-1}Xz_+$, the second equation of the chiral system (4) holds at $x$:
--
--   $$\bigl(D^+ + A\bigr)y_- = \bigl(c^{(\varsigma)}I + B^{(\varsigma)}\bigr)y_+ .$$
--
--   The proof applies the residual identity $D^+(Yv) + A(Yv) = Y\,D^+v$ for $Y = (X^*)^{-1}$ and the closed form $\operatorname{adj}(C) = (Q^2-M^2)^{-1}X^*(cI+B)X$, then cancels $(X^*)^{-1}X^* = I$.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eq. (7)/(8) and the text after (7); local source Atlas/Perturbations/Hintz2026/Equivalence4to7.lean at commit 8d059e0 (no public Git remote)

import Definitions.Def_Hintz2026_System4
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.system4_yminus_of_system7 (p : SubextremalKN) (zp zm : (Fin 2 -> ℝ) -> Fin 2 -> ℂ) (sg om mm : ℝ) (hzm : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => zm x j) (U p)) {x : Fin 2 -> ℝ} (hx : x ∈ U p) (h7 : (fun i => Dp p (fun z => zm z i) x) = adjugate (Cmat p sg om mm x) *ᵥ zp x) : (fun j => Dp p (fun z => (((X p z)ᴴ)⁻¹ *ᵥ zm z) j) x) + A p x *ᵥ (((X p x)ᴴ)⁻¹ *ᵥ zm x) = (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Bmat p sg om mm x) *ᵥ (((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ)⁻¹ • (X p x *ᵥ zp x)) := by sorry
