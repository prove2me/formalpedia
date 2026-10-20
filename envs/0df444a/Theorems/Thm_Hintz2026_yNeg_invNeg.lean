-- Prove2me | Theorems.Thm_Hintz2026_yNeg_invNeg
-- name    : Hintz2026.yNeg_invNeg
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T15:52:25.605807+00:00
-- url     : https://prove2.me/theorems/ad1c5199-663b-4a8b-ad03-e4fd7ff7b937
-- title:
--   The inverse chiral map is a right inverse (negative spin)
-- statement:
--   Throughout, $(M,a,Q)$ is a subextremal Kerr–Newman background ($M>0$, $Q\neq 0$, $a^2+Q^2<M^2$), $\Delta=r^2-2Mr+a^2+Q^2$, $\bar\rho=r+ia\cos\theta$, $\bar\rho^*=r-ia\cos\theta$, $U=\{r>r_+,\ 0<\theta<\pi\}$, and $D^-=\sqrt{\Delta}\,\partial_r-i\,\partial_\theta,\quad D^+=\sqrt{\Delta}\,\partial_r+i\,\partial_\theta$ act through coordinate-slice derivatives; the mode parameters are $\omega,m\in\mathbb{R}$. The chiral variables of eq. (3) are $y_\pm^{(+)}=\Delta^{5/4}\sqrt{\sin\theta}\,\bigl(\psi_2\pm i\Delta^{-1/2}\psi_1,\ -2Q(k\pm i\Delta^{-1/2}s)\bigr)$ (`yPos p (±1) F`) and $y_\pm^{(-)}=\Delta^{-3/4}\sqrt{\sin\theta}\,\bigl(\psi_{-2}\mp i\Delta^{1/2}\psi_{-1},\ 2Q(n\mp i\Delta^{1/2}\ell)\bigr)$ (`yNeg p (±1) G`). Define `invNeg` $=(\psi_{-2},\psi_{-1},n,\ell)$ by
--
--   $$\psi_{-2}=\frac{y_+^0+y_-^0}{2\,\mathrm{pre}},\quad \psi_{-1}=-\frac{y_+^0-y_-^0}{2i\sqrt{\Delta}\,\mathrm{pre}},\quad n=\frac{y_+^1+y_-^1}{4Q\,\mathrm{pre}},\quad \ell=-\frac{y_+^1-y_-^1}{4iQ\sqrt{\Delta}\,\mathrm{pre}},\qquad \mathrm{pre}=\Delta^{-3/4}\sqrt{\sin\theta}.$$
--
--   Then at every $z\in U$: $y_{\pm}^{(-)}(\mathrm{invNeg}(y_+,y_-))(z)=y_\pm(z)$.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eq. (3); local source Atlas/Perturbations/Hintz2026/MainTheorem.lean at commit aa3cc58 (no public Git remote)

import Definitions.Def_Hintz2026_Chiral
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.yNeg_invNeg (p : SubextremalKN) (yplus yminus : (Fin 2 -> ℝ) -> Fin 2 -> ℂ) {z : Fin 2 -> ℝ} (hz : z ∈ U p) : yNeg p 1 (invNeg p yplus yminus) z = yplus z ∧ yNeg p (-1) (invNeg p yplus yminus) z = yminus z := by sorry
