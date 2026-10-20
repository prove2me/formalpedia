-- Prove2me | Theorems.Thm_Hintz2026_main_pos_on_U
-- name    : Hintz2026.main_pos_on_U
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T15:52:26.992406+00:00
-- url     : https://prove2.me/theorems/c6d7b296-7a88-4c4a-8605-fd9f5d2fcc10
-- title:
--   Main theorem on all of $U$ (positive spin)
-- statement:
--   Throughout, $(M,a,Q)$ is a subextremal Kerr–Newman background ($M>0$, $Q\neq 0$, $a^2+Q^2<M^2$), $\Delta=r^2-2Mr+a^2+Q^2$, $\bar\rho=r+ia\cos\theta$, $\bar\rho^*=r-ia\cos\theta$, $U=\{r>r_+,\ 0<\theta<\pi\}$, and $D^-=\sqrt{\Delta}\,\partial_r-i\,\partial_\theta,\quad D^+=\sqrt{\Delta}\,\partial_r+i\,\partial_\theta$ act through coordinate-slice derivatives; the mode parameters are $\omega,m\in\mathbb{R}$. For $\omega,m\in\mathbb R$ and $F=(\psi_2,\psi_1,k,s)$ $C^\infty$ on $U$: system (1) holds at every point of $U$ if and only if system (7) with $\varsigma=+1$ holds at every point of $U$ for $z_+=\operatorname{adj}(X)\,y_+^{(+)}$, $z_-=X^*y_-^{(+)}$,
--
--   $$\bigl(\forall x\in U,\ \mathrm{Sys1PosAt}(\omega,m,F,x)\bigr)\iff\bigl(\forall x\in U,\ \mathrm{Sys7At}(+1,\omega,m,y_+^{(+)},y_-^{(+)},x)\bigr).$$
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eqs (1a)-(1d), (3), (4), (7); local source Atlas/Perturbations/Hintz2026/MainTheorem.lean at commit aa3cc58 (no public Git remote)

import Definitions.Def_Hintz2026_Chiral
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.main_pos_on_U (p : SubextremalKN) (om mm : ℝ) (F : PosFields) (hF : PosSmooth p F) : (∀ x ∈ U p, Sys1PosAt p om mm F x) ↔ (∀ x ∈ U p, Sys7At p 1 om mm (yPos p 1 F) (yPos p (-1) F) x) := by sorry
