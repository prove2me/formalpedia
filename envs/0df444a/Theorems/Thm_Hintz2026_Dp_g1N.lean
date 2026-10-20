-- Prove2me | Theorems.Thm_Hintz2026_Dp_g1N
-- name    : Hintz2026.Dp_g1N
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T15:52:19.506986+00:00
-- url     : https://prove2.me/theorems/c524dd0e-dc56-4d49-a187-b12bc6270ea0
-- title:
--   $D^+$ of the normalised chiral component $g_1$ (negative spin)
-- statement:
--   Throughout, $(M,a,Q)$ is a subextremal Kerr–Newman background ($M>0$, $Q\neq 0$, $a^2+Q^2<M^2$), $\Delta=r^2-2Mr+a^2+Q^2$, $\bar\rho=r+ia\cos\theta$, $\bar\rho^*=r-ia\cos\theta$, $U=\{r>r_+,\ 0<\theta<\pi\}$, and $D^-=\sqrt{\Delta}\,\partial_r-i\,\partial_\theta,\quad D^+=\sqrt{\Delta}\,\partial_r+i\,\partial_\theta$ act through coordinate-slice derivatives; the mode parameters are $\omega,m\in\mathbb{R}$. The negative-spin chiral variables of eq. (3) are $y_e^{(-)}=\Delta^{-3/4}\sqrt{\sin\theta}\,(g_1^{(e)},g_2^{(e)})$ with $g_1^{(e)}=\psi_{-2}-e\,i\sqrt{\Delta}\,\psi_{-1}$, $e=\pm1$. For fields $(\psi_{-2},\psi_{-1},n,\ell)$ slice-differentiable at $x\in U$ (`NegDiff`) and any real $e$,
--
--   $$D^+g_1^{(e)}=D^+\psi_{-2}-e\,i\Bigl(\sqrt{\Delta}\,D^+\psi_{-1}+\frac{\Delta'}{2}\psi_{-1}\Bigr).$$
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eq. (3); local source Atlas/Perturbations/Hintz2026/Eq1to4Neg.lean at commit aa3cc58 (no public Git remote)

import Definitions.Def_Hintz2026_Chiral
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.Dp_g1N (p : SubextremalKN) (e : ℝ) {G : NegFields} {x : Fin 2 -> ℝ} (hx : x ∈ U p) (hG : NegDiff G x) : Dp p (g1N p e G) x = Dp p G.psim2 x + (-(↑e * I)) * (↑(Real.sqrt (Del p (x 0))) * Dp p G.psim1 x + ↑(Del' p (x 0)) / 2 * G.psim1 x) := by sorry
