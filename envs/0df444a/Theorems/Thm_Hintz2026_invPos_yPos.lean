-- Prove2me | Theorems.Thm_Hintz2026_invPos_yPos
-- name    : Hintz2026.invPos_yPos
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T15:52:16.887981+00:00
-- url     : https://prove2.me/theorems/72e67e7b-a6f8-42ea-aa77-82f2271892d4
-- title:
--   The inverse chiral map is a left inverse (positive spin)
-- statement:
--   Throughout, $(M,a,Q)$ is a subextremal Kerr–Newman background ($M>0$, $Q\neq 0$, $a^2+Q^2<M^2$), $\Delta=r^2-2Mr+a^2+Q^2$, $\bar\rho=r+ia\cos\theta$, $\bar\rho^*=r-ia\cos\theta$, $U=\{r>r_+,\ 0<\theta<\pi\}$, and $D^-=\sqrt{\Delta}\,\partial_r-i\,\partial_\theta,\quad D^+=\sqrt{\Delta}\,\partial_r+i\,\partial_\theta$ act through coordinate-slice derivatives; the mode parameters are $\omega,m\in\mathbb{R}$. The chiral variables of eq. (3) are $y_\pm^{(+)}=\Delta^{5/4}\sqrt{\sin\theta}\,\bigl(\psi_2\pm i\Delta^{-1/2}\psi_1,\ -2Q(k\pm i\Delta^{-1/2}s)\bigr)$ (`yPos p (±1) F`) and $y_\pm^{(-)}=\Delta^{-3/4}\sqrt{\sin\theta}\,\bigl(\psi_{-2}\mp i\Delta^{1/2}\psi_{-1},\ 2Q(n\mp i\Delta^{1/2}\ell)\bigr)$ (`yNeg p (±1) G`). With `invPos` as in `yPos_invPos`, for any fields $F=(\psi_2,\psi_1,k,s)$ and every $z\in U$, applying `invPos` to $(y_+^{(+)},y_-^{(+)})$ returns the four original field values at $z$: $\psi_2(z),\psi_1(z),k(z),s(z)$.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eq. (3); local source Atlas/Perturbations/Hintz2026/MainTheorem.lean at commit aa3cc58 (no public Git remote)

import Definitions.Def_Hintz2026_Chiral
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.invPos_yPos (p : SubextremalKN) (F : PosFields) {z : Fin 2 -> ℝ} (hz : z ∈ U p) : (invPos p (yPos p 1 F) (yPos p (-1) F)).psi2 z = F.psi2 z ∧ (invPos p (yPos p 1 F) (yPos p (-1) F)).psi1 z = F.psi1 z ∧ (invPos p (yPos p 1 F) (yPos p (-1) F)).k z = F.k z ∧ (invPos p (yPos p 1 F) (yPos p (-1) F)).s z = F.s z := by sorry
