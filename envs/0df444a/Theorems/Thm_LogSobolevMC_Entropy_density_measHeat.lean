-- Prove2me | Theorems.Thm_LogSobolevMC_Entropy_density_measHeat
-- name    : LogSobolevMC.Entropy.density_measHeat
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:07:26.642911+00:00
-- url     : https://prove2.me/theorems/e06240e4-4b1e-4bb7-9571-21ebf24c235a
-- title:
--   §2.1, Remarks (ii), p. 702 — if μ = fπ, the measure μH_t has density H_t^*f with respect to π
-- statement:
--   Let $K$ be a Markov kernel on a finite set $\mathcal X$ with invariant probability $\pi$, $\pi(x)>0$ for all $x$. The adjoint of $K$ in $\ell^2(\pi)$ is the kernel $K^*(x,y)=K(y,x)\pi(y)/\pi(x)$, and $H_t^*=e^{-t(I-K^*)}$ is its heat semigroup. For every function $f$ on $\mathcal X$ and every real $t$, the measure $\mu=f\pi$ transported by the semigroup has density $H_t^*f$:
--
--   $$\sum_x H_t(x,y)\,f(x)\pi(x)=\big(H_t^*f\big)(y)\,\pi(y)\qquad\text{for all }y\in\mathcal X.$$
--
--   This identity converts the evolution of measures $\mu\mapsto\mu H_t$ into the evolution of densities $f\mapsto H_t^*f$, which is the first step of the proof of the entropy decay Theorem 3.6.
--
--   **Formalization Note** The identity is stated for every real $f$ (not only probability densities) and every real $t$; it is an identity of finite sums. $K^*$ is the published `MarkovMixing.timeReversal K π`.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 702, §2.1, Remarks (ii); adjoint K^* on p. 701

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_continuous
import Definitions.Def_LogSobolevMC_Entropy_Setting

namespace LogSobolevMC.Entropy

theorem density_measHeat {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π) (hπpos : ∀ x, 0 < π x)
    (f : V → ℝ) (t : ℝ) :
    measHeat K t (fun x => f x * π x) =
      fun y => LogSobolevMC.ChiSquare.heatOp (MarkovMixing.timeReversal K π) t f y * π y := by sorry

end LogSobolevMC.Entropy
