-- Prove2me | Theorems.Thm_Hintz2026_Dm_div_sqrtDel
-- name    : Hintz2026.Dm_div_sqrtDel
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T15:52:15.782976+00:00
-- url     : https://prove2.me/theorems/2e6ef9c3-14fd-4acf-9dbe-734907bf9e12
-- title:
--   $D^-$ of a quotient by $\sqrt{\Delta}$
-- statement:
--   Throughout, $(M,a,Q)$ is a subextremal Kerr–Newman background ($M>0$, $Q\neq 0$, $a^2+Q^2<M^2$), $\Delta=r^2-2Mr+a^2+Q^2$, $\bar\rho=r+ia\cos\theta$, $\bar\rho^*=r-ia\cos\theta$, $U=\{r>r_+,\ 0<\theta<\pi\}$, and $D^-=\sqrt{\Delta}\,\partial_r-i\,\partial_\theta,\quad D^+=\sqrt{\Delta}\,\partial_r+i\,\partial_\theta$ act through coordinate-slice derivatives; the mode parameters are $\omega,m\in\mathbb{R}$. For a field $f$ slice-differentiable at $x\in U$,
--
--   $$D^-\Bigl(\frac{f}{\sqrt{\Delta}}\Bigr)=\frac{D^-f}{\sqrt{\Delta}}-\frac{\Delta'}{2\Delta}\,f,\qquad \Delta'=2(r-M),$$
--
--   since $\partial_r\sqrt{\Delta}=(r-M)/\sqrt{\Delta}$ and $\sqrt{\Delta}$ does not depend on $\theta$. This is the derivative rule for the $\Delta^{-1/2}$ factors inside the chiral variables of eq. (3).
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eq. (3); local source Atlas/Perturbations/Hintz2026/Eq1to4Identity.lean at commit aa3cc58 (no public Git remote)

import Definitions.Def_Hintz2026_Chiral
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.Dm_div_sqrtDel (p : SubextremalKN) {x : Fin 2 -> ℝ} (hx : x ∈ U p) (f : (Fin 2 -> ℝ) -> ℂ) (hf : ∀ k, DifferentiableAt ℝ (fun u => f (update x k u)) (x k)) : Dm p (fun z => f z / ↑(Real.sqrt (Del p (z 0)))) x = Dm p f x / ↑(Real.sqrt (Del p (x 0))) - f x * ↑(Del' p (x 0)) / (2 * ↑(Del p (x 0))) := by sorry
