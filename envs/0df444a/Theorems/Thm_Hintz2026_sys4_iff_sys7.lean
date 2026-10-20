-- Prove2me | Theorems.Thm_Hintz2026_sys4_iff_sys7
-- name    : Hintz2026.sys4_iff_sys7
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T15:52:45.901981+00:00
-- url     : https://prove2.me/theorems/c50987bd-c6aa-4090-b239-043189c3657c
-- title:
--   Local equivalence (4) ⟺ (7) in predicate form
-- statement:
--   Throughout, $(M,a,Q)$ is a subextremal Kerr–Newman background ($M>0$, $Q\neq 0$, $a^2+Q^2<M^2$), $\Delta=r^2-2Mr+a^2+Q^2$, $\bar\rho=r+ia\cos\theta$, $\bar\rho^*=r-ia\cos\theta$, $U=\{r>r_+,\ 0<\theta<\pi\}$, and $D^-=\sqrt{\Delta}\,\partial_r-i\,\partial_\theta,\quad D^+=\sqrt{\Delta}\,\partial_r+i\,\partial_\theta$ act through coordinate-slice derivatives; the mode parameters are $\omega,m\in\mathbb{R}$. System (4) with spin parameter $\varsigma$ is
--
--   $$(\sqrt{\Delta}\partial_r\mp i\partial_\theta\mp A)\,y_\pm=(c^{(\varsigma)}I\mp B^{(\varsigma)})\,y_\mp,$$
--
--   with $A$, $B^{(\varsigma)}$, $c^{(\varsigma)}$ the explicit coefficient data of Hintz eq. (4) (`A`, `Bmat`, `cscalar`); `Sys4At` is the pair of these vector equations at a point. System (7) for the transformed variables $z_+=\operatorname{adj}(X)\,y_+$ and $z_-=X^*y_-$ (with $X$ the matrix integrating factor of eq. (5) and $\operatorname{adj}X=\det X\cdot X^{-1}$ since $\det X=Q^2-M^2$ is constant) is
--
--   $$D^-z_+=C^{(\varsigma)}z_-,\qquad D^+z_-=\operatorname{adj}(C^{(\varsigma)})\,z_+,\qquad C^{(\varsigma)}=\det X\cdot X^{-1}(c^{(\varsigma)}I-B^{(\varsigma)})(X^*)^{-1};$$
--
--   `Sys7At` is this pair of equations at a point.
--
--   For any real $\varsigma,\omega,m$ and fields $y_+,y_-$ whose components are $C^\infty$ on $U$, at every $x\in U$:
--
--   $$\mathrm{Sys4At}(\varsigma,\omega,m,y_+,y_-,x)\iff\mathrm{Sys7At}(\varsigma,\omega,m,y_+,y_-,x).$$
--
--   This restates the platform theorem `Hintz2026.system4_iff_system7` through the predicates `Sys4At` and `Sys7At`.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eqs (4), (7); local source Atlas/Perturbations/Hintz2026/MainTheorem.lean at commit aa3cc58 (no public Git remote)

import Definitions.Def_Hintz2026_Chiral
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.sys4_iff_sys7 (p : SubextremalKN) (sg om mm : ℝ) (yplus yminus : (Fin 2 -> ℝ) -> Fin 2 -> ℂ) (hyp : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => yplus x j) (U p)) (hym : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => yminus x j) (U p)) {x : Fin 2 -> ℝ} (hx : x ∈ U p) : Sys4At p sg om mm yplus yminus x ↔ Sys7At p sg om mm yplus yminus x := by sorry
