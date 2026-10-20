-- Prove2me | Theorems.Thm_Hintz2026_system7_zplus_of_system4
-- name    : Hintz2026.system7_zplus_of_system4
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T14:53:15.468977+00:00
-- url     : https://prove2.me/theorems/139551b3-029f-45dd-8d7c-39e0dff757a3
-- title:
--   System (4) $\Rightarrow$ system (7), $z_+$ equation
-- statement:
--   Let $y_+, y_-\colon U\to\mathbb{C}^2$ be $C^\infty$ fields on $U$ and $x\in U$. Suppose the first equation of Hintz's chiral system (4) holds at $x$:
--
--   $$\bigl(D^- - A\bigr)y_+ = \bigl(c^{(\varsigma)}I - B^{(\varsigma)}\bigr)y_- .$$
--
--   Then the transformed variables $z_+ = \operatorname{adj}(X)\,y_+$ and $z_- = X^*y_-$ of eq. (7) satisfy at $x$
--
--   $$D^- z_+ = C^{(\varsigma)}\,z_- ,$$
--
--   with $C^{(\varsigma)} = (\det X)X^{-1}(c^{(\varsigma)}I - B^{(\varsigma)})(X^*)^{-1}$. The proof applies the Leibniz rule for $D^-$ to $\operatorname{adj}(X)y_+$, uses $D^-(\operatorname{adj}X) = -(\operatorname{adj}X)A$ to cancel the $A$-term, and then the identity $C X^* = \operatorname{adj}(X)(cI-B)$. (Here $z_+ = \operatorname{adj}(X)y_+$ agrees with the paper's $(\det X)X^{-1}y_+$ because $\det X = Q^2-M^2$ is constant.)
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eq. (7)/(8) and the text after (7); local source Atlas/Perturbations/Hintz2026/Equivalence4to7.lean at commit 8d059e0 (no public Git remote)

import Definitions.Def_Hintz2026_System4
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.system7_zplus_of_system4 (p : SubextremalKN) (yplus yminus : (Fin 2 -> ℝ) -> Fin 2 -> ℂ) (sg om mm : ℝ) (hyp : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => yplus x j) (U p)) (hym : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => yminus x j) (U p)) {x : Fin 2 -> ℝ} (hx : x ∈ U p) (h4 : (fun j => Dm p (fun z => yplus z j) x) - A p x *ᵥ yplus x = (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Bmat p sg om mm x) *ᵥ yminus x) : (fun i => Dm p (fun z => (adjugate (X p z) *ᵥ yplus z) i) x) = Cmat p sg om mm x *ᵥ zminus p yminus x := by sorry
