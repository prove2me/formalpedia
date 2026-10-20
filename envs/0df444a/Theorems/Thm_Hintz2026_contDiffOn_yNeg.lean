-- Prove2me | Theorems.Thm_Hintz2026_contDiffOn_yNeg
-- name    : Hintz2026.contDiffOn_yNeg
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T15:53:00.388867+00:00
-- url     : https://prove2.me/theorems/4211a560-36d7-450f-9ec8-e3b058b6bcf4
-- title:
--   The negative-spin chiral variables are $C^\infty$ on $U$
-- statement:
--   Throughout, $(M,a,Q)$ is a subextremal Kerr–Newman background ($M>0$, $Q\neq 0$, $a^2+Q^2<M^2$), $\Delta=r^2-2Mr+a^2+Q^2$, $\bar\rho=r+ia\cos\theta$, $\bar\rho^*=r-ia\cos\theta$, $U=\{r>r_+,\ 0<\theta<\pi\}$, and $D^-=\sqrt{\Delta}\,\partial_r-i\,\partial_\theta,\quad D^+=\sqrt{\Delta}\,\partial_r+i\,\partial_\theta$ act through coordinate-slice derivatives; the mode parameters are $\omega,m\in\mathbb{R}$. The chiral variables of eq. (3) are $y_\pm^{(+)}=\Delta^{5/4}\sqrt{\sin\theta}\,\bigl(\psi_2\pm i\Delta^{-1/2}\psi_1,\ -2Q(k\pm i\Delta^{-1/2}s)\bigr)$ (`yPos p (±1) F`) and $y_\pm^{(-)}=\Delta^{-3/4}\sqrt{\sin\theta}\,\bigl(\psi_{-2}\mp i\Delta^{1/2}\psi_{-1},\ 2Q(n\mp i\Delta^{1/2}\ell)\bigr)$ (`yNeg p (±1) G`).
--
--   If $\psi_{-2},\psi_{-1},n,\ell$ are $C^\infty$ on $U$ (`NegSmooth`), then for every real $e$ and each component $j$ the function $x\mapsto y_e^{(-)}(x)_j$ is $C^\infty$ on $U$.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eq. (3); local source Atlas/Perturbations/Hintz2026/ChiralSmooth.lean at commit aa3cc58 (no public Git remote)

import Definitions.Def_Hintz2026_Chiral
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.contDiffOn_yNeg (p : SubextremalKN) {G : NegFields} (hG : NegSmooth p G) (e : ℝ) (j : Fin 2) : ContDiffOn ℝ ∞ (fun x => yNeg p e G x j) (U p) := by sorry
