-- Prove2me | Theorems.Thm_Hintz2026_yPos_invPos
-- name    : Hintz2026.yPos_invPos
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T15:52:28.297603+00:00
-- url     : https://prove2.me/theorems/80400ab1-9eff-41eb-826d-66233bdc173d
-- title:
--   The inverse chiral map is a right inverse (positive spin)
-- statement:
--   Throughout, $(M,a,Q)$ is a subextremal Kerr–Newman background ($M>0$, $Q\neq 0$, $a^2+Q^2<M^2$), $\Delta=r^2-2Mr+a^2+Q^2$, $\bar\rho=r+ia\cos\theta$, $\bar\rho^*=r-ia\cos\theta$, $U=\{r>r_+,\ 0<\theta<\pi\}$, and $D^-=\sqrt{\Delta}\,\partial_r-i\,\partial_\theta,\quad D^+=\sqrt{\Delta}\,\partial_r+i\,\partial_\theta$ act through coordinate-slice derivatives; the mode parameters are $\omega,m\in\mathbb{R}$. The chiral variables of eq. (3) are $y_\pm^{(+)}=\Delta^{5/4}\sqrt{\sin\theta}\,\bigl(\psi_2\pm i\Delta^{-1/2}\psi_1,\ -2Q(k\pm i\Delta^{-1/2}s)\bigr)$ (`yPos p (±1) F`) and $y_\pm^{(-)}=\Delta^{-3/4}\sqrt{\sin\theta}\,\bigl(\psi_{-2}\mp i\Delta^{1/2}\psi_{-1},\ 2Q(n\mp i\Delta^{1/2}\ell)\bigr)$ (`yNeg p (±1) G`). Define, for a pair of fields $(y_+,y_-)$, `invPos` $=(\psi_2,\psi_1,k,s)$ by
--
--   $$\psi_2=\frac{y_+^0+y_-^0}{2\,\mathrm{pre}},\quad \psi_1=\frac{\sqrt{\Delta}\,(y_+^0-y_-^0)}{2i\,\mathrm{pre}},\quad k=-\frac{y_+^1+y_-^1}{4Q\,\mathrm{pre}},\quad s=-\frac{\sqrt{\Delta}\,(y_+^1-y_-^1)}{4iQ\,\mathrm{pre}},\qquad \mathrm{pre}=\Delta^{5/4}\sqrt{\sin\theta}.$$
--
--   Then at every $z\in U$: $y_{+}^{(+)}(\mathrm{invPos}(y_+,y_-))(z)=y_+(z)$ and $y_{-}^{(+)}(\mathrm{invPos}(y_+,y_-))(z)=y_-(z)$.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eq. (3); local source Atlas/Perturbations/Hintz2026/MainTheorem.lean at commit aa3cc58 (no public Git remote)

import Definitions.Def_Hintz2026_Chiral
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.yPos_invPos (p : SubextremalKN) (yplus yminus : (Fin 2 -> ℝ) -> Fin 2 -> ℂ) {z : Fin 2 -> ℝ} (hz : z ∈ U p) : yPos p 1 (invPos p yplus yminus) z = yplus z ∧ yPos p (-1) (invPos p yplus yminus) z = yminus z := by sorry
