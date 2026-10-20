-- Prove2me | Theorems.Thm_Hintz2026_contDiffOn_yPos
-- name    : Hintz2026.contDiffOn_yPos
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T15:52:24.149615+00:00
-- url     : https://prove2.me/theorems/7aea9685-ffe3-41ba-a7b3-5226553659d7
-- title:
--   The positive-spin chiral variables are $C^\infty$ on $U$
-- statement:
--   Throughout, $(M,a,Q)$ is a subextremal Kerr–Newman background ($M>0$, $Q\neq 0$, $a^2+Q^2<M^2$), $\Delta=r^2-2Mr+a^2+Q^2$, $\bar\rho=r+ia\cos\theta$, $\bar\rho^*=r-ia\cos\theta$, $U=\{r>r_+,\ 0<\theta<\pi\}$, and $D^-=\sqrt{\Delta}\,\partial_r-i\,\partial_\theta,\quad D^+=\sqrt{\Delta}\,\partial_r+i\,\partial_\theta$ act through coordinate-slice derivatives; the mode parameters are $\omega,m\in\mathbb{R}$. The chiral variables of eq. (3) are $y_\pm^{(+)}=\Delta^{5/4}\sqrt{\sin\theta}\,\bigl(\psi_2\pm i\Delta^{-1/2}\psi_1,\ -2Q(k\pm i\Delta^{-1/2}s)\bigr)$ (`yPos p (±1) F`) and $y_\pm^{(-)}=\Delta^{-3/4}\sqrt{\sin\theta}\,\bigl(\psi_{-2}\mp i\Delta^{1/2}\psi_{-1},\ 2Q(n\mp i\Delta^{1/2}\ell)\bigr)$ (`yNeg p (±1) G`).
--
--   If $\psi_2,\psi_1,k,s$ are $C^\infty$ on $U$ (`PosSmooth`), then for every real $e$ and each component $j\in\{0,1\}$ the function $x\mapsto y_e^{(+)}(x)_j$ is $C^\infty$ on $U$. This uses $\Delta>0$ and $\sin\theta>0$ on $U$, so that $\Delta^{5/4}$, $\sqrt{\sin\theta}$ and $1/\sqrt{\Delta}$ are smooth there.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eq. (3); local source Atlas/Perturbations/Hintz2026/ChiralSmooth.lean at commit aa3cc58 (no public Git remote)

import Definitions.Def_Hintz2026_Chiral
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.contDiffOn_yPos (p : SubextremalKN) {F : PosFields} (hF : PosSmooth p F) (e : ℝ) (j : Fin 2) : ContDiffOn ℝ ∞ (fun x => yPos p e F x j) (U p) := by sorry
