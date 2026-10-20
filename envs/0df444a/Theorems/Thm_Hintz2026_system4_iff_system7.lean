-- Prove2me | Theorems.Thm_Hintz2026_system4_iff_system7
-- name    : Hintz2026.system4_iff_system7
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T14:53:21.864595+00:00
-- url     : https://prove2.me/theorems/0afd6f90-fa39-4d1f-bc38-bbf8238651e3
-- title:
--   Local equivalence of the chiral system (4) and the transformed system (7)
-- statement:
--   Fix a subextremal Kerr–Newman background ($M>0$, $Q\neq 0$, $a^2+Q^2<M^2$), the domain $U=\{r>r_+,\ 0<\theta<\pi\}$, a real frequency $\omega$, a real azimuthal number $m$, and a real spin parameter $\varsigma$ (the paper's positive- and negative-spin systems are the instances $\varsigma=+1$ and $\varsigma=-1$). Let $y_+, y_-\colon U\to\mathbb{C}^2$ be $C^\infty$ fields and $x\in U$. Then the two statements below are equivalent.
--
--   **System (4) at $x$** (Hintz eq. (4), both equations):
--
--   $$\bigl(D^- - A\bigr)y_+ = \bigl(c^{(\varsigma)}I - B^{(\varsigma)}\bigr)y_- ,\qquad \bigl(D^+ + A\bigr)y_- = \bigl(c^{(\varsigma)}I + B^{(\varsigma)}\bigr)y_+ ,$$
--
--   where $D^- = \sqrt{\Delta}\,\partial_r-i\,\partial_\theta,\quad D^+ = \sqrt{\Delta}\,\partial_r+i\,\partial_\theta$, $A$ is the Hermitian off-diagonal matrix of eq. (4), $c^{(\varsigma)} = \bigl(\varsigma\tfrac{iK}{\Delta} + \tfrac{3}{\bar\rho^*} - \tfrac{3\Delta'}{4\Delta}\bigr)\sqrt{\Delta}$ and $B^{(\varsigma)}$ is the traceless matrix of eq. (4).
--
--   **System (7) at $x$** for the transformed variables $z_+ := \operatorname{adj}(X)\,y_+$ (which equals $(\det X)X^{-1}y_+$) and $z_- := X^*y_-$:
--
--   $$D^- z_+ = C^{(\varsigma)}\,z_- ,\qquad D^+ z_- = \operatorname{adj}\bigl(C^{(\varsigma)}\bigr)\,z_+ ,$$
--
--   with $C^{(\varsigma)} = (\det X)X^{-1}(c^{(\varsigma)}I - B^{(\varsigma)})(X^*)^{-1}$.
--
--   The forward direction is the two transport lemmas for $z_\pm$; the backward direction applies the inverse-transformation lemmas to $z_\pm$ and then uses the round trips $(Q^2-M^2)^{-1}X\operatorname{adj}(X) = I$ and $(X^*)^{-1}X^* = I$ on $U$, together with the locality of $D^\pm$ (they depend only on values in $U$). Both spin directions are covered by the single real parameter $\varsigma$; no frequency or mode restriction beyond $\omega, m\in\mathbb{R}$ is used. Together with `Cmat_eq_Csep` and `adjugate_Csep_eq`, this yields the separated-coefficient version of (7), from which the paper writes the block form (8). This theorem itself is the (4) iff (7) statement; it is not a separate theorem about the full four-component differential operator in (8), nor about spectral separation.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eq. (7)/(8) and the text after (7); local source Atlas/Perturbations/Hintz2026/Equivalence4to7.lean at commit 8d059e0 (no public Git remote)

import Definitions.Def_Hintz2026_System4
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.system4_iff_system7 (p : SubextremalKN) (yplus yminus : (Fin 2 -> ℝ) -> Fin 2 -> ℂ) (sg om mm : ℝ) (hyp : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => yplus x j) (U p)) (hym : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => yminus x j) (U p)) {x : Fin 2 -> ℝ} (hx : x ∈ U p) : ((fun j => Dm p (fun z => yplus z j) x) - A p x *ᵥ yplus x = (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Bmat p sg om mm x) *ᵥ yminus x ∧ (fun j => Dp p (fun z => yminus z j) x) + A p x *ᵥ yminus x = (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Bmat p sg om mm x) *ᵥ yplus x) ↔ ((fun i => Dm p (fun z => (adjugate (X p z) *ᵥ yplus z) i) x) = Cmat p sg om mm x *ᵥ ((X p x)ᴴ *ᵥ yminus x) ∧ (fun i => Dp p (fun z => ((X p z)ᴴ *ᵥ yminus z) i) x) = adjugate (Cmat p sg om mm x) *ᵥ (adjugate (X p x) *ᵥ yplus x)) := by sorry
