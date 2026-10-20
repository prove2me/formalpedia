-- Prove2me | Theorems.Thm_Hintz2026_Dm_g1
-- name    : Hintz2026.Dm_g1
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T15:52:13.454788+00:00
-- url     : https://prove2.me/theorems/8b804af0-2552-4c62-9e76-a6fb5573133d
-- title:
--   $D^-$ of the normalised chiral component $g_1$ (positive spin)
-- statement:
--   Throughout, $(M,a,Q)$ is a subextremal Kerr–Newman background ($M>0$, $Q\neq 0$, $a^2+Q^2<M^2$), $\Delta=r^2-2Mr+a^2+Q^2$, $\bar\rho=r+ia\cos\theta$, $\bar\rho^*=r-ia\cos\theta$, $U=\{r>r_+,\ 0<\theta<\pi\}$, and $D^-=\sqrt{\Delta}\,\partial_r-i\,\partial_\theta,\quad D^+=\sqrt{\Delta}\,\partial_r+i\,\partial_\theta$ act through coordinate-slice derivatives; the mode parameters are $\omega,m\in\mathbb{R}$. The positive-spin chiral variables of eq. (3) are $y_e^{(+)}=\Delta^{5/4}\sqrt{\sin\theta}\,(g_1^{(e)},g_2^{(e)})$ with $g_1^{(e)}=\psi_2+e\,i\,\psi_1/\sqrt{\Delta}$, $e=\pm1$. For fields $(\psi_2,\psi_1,k,s)$ slice-differentiable at $x\in U$ (`PosDiff`) and any real $e$,
--
--   $$D^-g_1^{(e)}=D^-\psi_2+e\,i\Bigl(\frac{D^-\psi_1}{\sqrt{\Delta}}-\frac{\Delta'}{2\Delta}\psi_1\Bigr).$$
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eq. (3); local source Atlas/Perturbations/Hintz2026/Eq1to4Identity.lean at commit aa3cc58 (no public Git remote)

import Definitions.Def_Hintz2026_Chiral
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.Dm_g1 (p : SubextremalKN) (e : ℝ) {F : PosFields} {x : Fin 2 -> ℝ} (hx : x ∈ U p) (hF : PosDiff F x) : Dm p (g1 p e F) x = Dm p F.psi2 x + (↑e * I) * (Dm p F.psi1 x / ↑(Real.sqrt (Del p (x 0))) - F.psi1 x * ↑(Del' p (x 0)) / (2 * ↑(Del p (x 0)))) := by sorry
