-- Prove2me | Theorems.Thm_Hintz2026_invNeg_yNeg
-- name    : Hintz2026.invNeg_yNeg
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T15:52:34.875575+00:00
-- url     : https://prove2.me/theorems/1139e27b-3cc7-403c-b8e8-96d8342660c2
-- title:
--   The inverse chiral map is a left inverse (negative spin)
-- statement:
--   Throughout, $(M,a,Q)$ is a subextremal Kerr–Newman background ($M>0$, $Q\neq 0$, $a^2+Q^2<M^2$), $\Delta=r^2-2Mr+a^2+Q^2$, $\bar\rho=r+ia\cos\theta$, $\bar\rho^*=r-ia\cos\theta$, $U=\{r>r_+,\ 0<\theta<\pi\}$, and $D^-=\sqrt{\Delta}\,\partial_r-i\,\partial_\theta,\quad D^+=\sqrt{\Delta}\,\partial_r+i\,\partial_\theta$ act through coordinate-slice derivatives; the mode parameters are $\omega,m\in\mathbb{R}$. The chiral variables of eq. (3) are $y_\pm^{(+)}=\Delta^{5/4}\sqrt{\sin\theta}\,\bigl(\psi_2\pm i\Delta^{-1/2}\psi_1,\ -2Q(k\pm i\Delta^{-1/2}s)\bigr)$ (`yPos p (±1) F`) and $y_\pm^{(-)}=\Delta^{-3/4}\sqrt{\sin\theta}\,\bigl(\psi_{-2}\mp i\Delta^{1/2}\psi_{-1},\ 2Q(n\mp i\Delta^{1/2}\ell)\bigr)$ (`yNeg p (±1) G`). With `invNeg` as in `yNeg_invNeg`, for any fields $G=(\psi_{-2},\psi_{-1},n,\ell)$ and every $z\in U$, applying `invNeg` to $(y_+^{(-)},y_-^{(-)})$ returns $\psi_{-2}(z),\psi_{-1}(z),n(z),\ell(z)$.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eq. (3); local source Atlas/Perturbations/Hintz2026/MainTheorem.lean at commit aa3cc58 (no public Git remote)

import Definitions.Def_Hintz2026_Chiral
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.invNeg_yNeg (p : SubextremalKN) (G : NegFields) {z : Fin 2 -> ℝ} (hz : z ∈ U p) : (invNeg p (yNeg p 1 G) (yNeg p (-1) G)).psim2 z = G.psim2 z ∧ (invNeg p (yNeg p 1 G) (yNeg p (-1) G)).psim1 z = G.psim1 z ∧ (invNeg p (yNeg p 1 G) (yNeg p (-1) G)).n z = G.n z ∧ (invNeg p (yNeg p 1 G) (yNeg p (-1) G)).l z = G.l z := by sorry
