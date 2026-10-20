-- Prove2me | Theorems.Thm_Hintz2026_system7_zminus_of_system4
-- name    : Hintz2026.system7_zminus_of_system4
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T14:53:24.253981+00:00
-- url     : https://prove2.me/theorems/6d281dd1-5d38-4edc-8d7c-b00a13c0e6c6
-- title:
--   System (4) $\Rightarrow$ system (7), $z_-$ equation
-- statement:
--   Let $y_+, y_-\colon U\to\mathbb{C}^2$ be $C^\infty$ fields on $U$ and $x\in U$. Suppose the second equation of Hintz's chiral system (4) holds at $x$:
--
--   $$\bigl(D^+ + A\bigr)y_- = \bigl(c^{(\varsigma)}I + B^{(\varsigma)}\bigr)y_+ .$$
--
--   Then $z_- = X^*y_-$ and $z_+ = \operatorname{adj}(X)\,y_+$ satisfy at $x$
--
--   $$D^+ z_- = \operatorname{adj}\bigl(C^{(\varsigma)}\bigr)\,z_+ .$$
--
--   The proof uses the Leibniz rule for $D^+$, $D^+(X^*) = X^*A$ to cancel the $A$-term, and the closed form $\operatorname{adj}(C) = (Q^2-M^2)^{-1}X^*(cI+B)X$ together with $X\operatorname{adj}(X) = (Q^2-M^2)I$.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eq. (7)/(8) and the text after (7); local source Atlas/Perturbations/Hintz2026/Equivalence4to7.lean at commit 8d059e0 (no public Git remote)

import Definitions.Def_Hintz2026_System4
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.system7_zminus_of_system4 (p : SubextremalKN) (yplus yminus : (Fin 2 -> ℝ) -> Fin 2 -> ℂ) (sg om mm : ℝ) (hyp : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => yplus x j) (U p)) (hym : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => yminus x j) (U p)) {x : Fin 2 -> ℝ} (hx : x ∈ U p) (h4 : (fun j => Dp p (fun z => yminus z j) x) + A p x *ᵥ yminus x = (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Bmat p sg om mm x) *ᵥ yplus x) : (fun i => Dp p (fun z => ((X p z)ᴴ *ᵥ yminus z) i) x) = adjugate (Cmat p sg om mm x) *ᵥ zplus p yplus x := by sorry
