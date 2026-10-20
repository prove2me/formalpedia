-- Prove2me | Theorems.Thm_Hintz2026_main_neg_on_U
-- name    : Hintz2026.main_neg_on_U
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T15:52:21.215652+00:00
-- url     : https://prove2.me/theorems/4cca999a-179e-4f87-b8e5-92e9b0de6ee7
-- title:
--   Main theorem on all of $U$ (negative spin)
-- statement:
--   Throughout, $(M,a,Q)$ is a subextremal Kerr–Newman background ($M>0$, $Q\neq 0$, $a^2+Q^2<M^2$), $\Delta=r^2-2Mr+a^2+Q^2$, $\bar\rho=r+ia\cos\theta$, $\bar\rho^*=r-ia\cos\theta$, $U=\{r>r_+,\ 0<\theta<\pi\}$, and $D^-=\sqrt{\Delta}\,\partial_r-i\,\partial_\theta,\quad D^+=\sqrt{\Delta}\,\partial_r+i\,\partial_\theta$ act through coordinate-slice derivatives; the mode parameters are $\omega,m\in\mathbb{R}$. For $\omega,m\in\mathbb R$ and $G=(\psi_{-2},\psi_{-1},n,\ell)$ $C^\infty$ on $U$:
--
--   $$\bigl(\forall x\in U,\ \mathrm{Sys1NegAt}(\omega,m,G,x)\bigr)\iff\bigl(\forall x\in U,\ \mathrm{Sys7At}(-1,\omega,m,y_+^{(-)},y_-^{(-)},x)\bigr).$$
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eqs (1a)-(1d) with the negative-spin replacement rules, (3), (4), (7); local source Atlas/Perturbations/Hintz2026/MainTheorem.lean at commit aa3cc58 (no public Git remote)

import Definitions.Def_Hintz2026_Chiral
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.main_neg_on_U (p : SubextremalKN) (om mm : ℝ) (G : NegFields) (hG : NegSmooth p G) : (∀ x ∈ U p, Sys1NegAt p om mm G x) ↔ (∀ x ∈ U p, Sys7At p (-1) om mm (yNeg p 1 G) (yNeg p (-1) G) x) := by sorry
