-- Prove2me | Theorems.Thm_LogSobolevMC_Entropy_theorem_3_6
-- name    : LogSobolevMC.Entropy.theorem_3_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:07:38.378974+00:00
-- url     : https://prove2.me/theorems/05da7619-2ec8-41fe-8381-6b0f9db1268b
-- title:
--   Theorem 3.6, p. 722 — Ent_π(μH_t) ≤ Ent_π(μ)e^{−2αt}, and ≤ Ent_π(μ)e^{−4αt} when (K, π) is reversible
-- statement:
--   Let $K$ be a Markov kernel on a finite set $\mathcal X$ with invariant probability $\pi$, $\pi(x)>0$ for all $x$, and let $\alpha$ be its log-Sobolev constant,
--   $$\alpha=\inf\Big\{\frac{\mathcal E(f,f)}{\mathcal L(f)}:\ \mathcal L(f)\neq0\Big\},$$
--   where $\mathcal E(f,f)=\langle (I-K)f,f\rangle_\pi$ and $\mathcal L(f)=\sum_x|f(x)|^2\log\big(|f(x)|^2/\|f\|_2^2\big)\pi(x)$. Let $H_t=e^{-t(I-K)}$ and, for a probability measure $\mu$ on $\mathcal X$, let $\mu H_t(y)=\sum_x H_t(x,y)\mu(x)$. Write $\mathrm{Ent}_\pi(\nu)=\sum_x\nu(x)\log\frac{\nu(x)}{\pi(x)}$ for the relative entropy. Then for every probability measure $\mu$:
--
--   1. $$\mathrm{Ent}_\pi(\mu H_t)\le \mathrm{Ent}_\pi(\mu)\,e^{-2\alpha t}\qquad\text{for all }t>0;$$
--   2. if $(K,\pi)$ is reversible ($\pi(x)K(x,y)=\pi(y)K(y,x)$ for all $x,y$), then
--   $$\mathrm{Ent}_\pi(\mu H_t)\le \mathrm{Ent}_\pi(\mu)\,e^{-4\alpha t}\qquad\text{for all }t>0.$$
--
--   The log-Sobolev constant is thus an exponential rate of convergence to stationarity in relative entropy, for every initial distribution. Combined with Pinsker's inequality it gives total variation bounds such as (3.3).
--
--   **Formalization Note** The chain is not assumed irreducible: the statement holds for every stochastic $K$ with a positive invariant probability (for a reducible chain $\alpha=0$ and the claim is that entropy does not increase). $\alpha$ is a real infimum, which is $0$ on a one-point space; no positivity of $\alpha$ is assumed.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 722, Theorem 3.6

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_continuous
import Definitions.Def_LogSobolevMC_Entropy_Setting

namespace LogSobolevMC.Entropy

theorem theorem_3_6 {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π) (hπpos : ∀ x, 0 < π x)
    (μ : V → ℝ) (hμ : MarkovMixing.IsDist μ) :
    (∀ t : ℝ, 0 < t →
        relEnt π (measHeat K t μ) ≤ relEnt π μ * Real.exp (-2 * LogSobolevMC.ChiSquare.logSobolev K π * t)) ∧
      (MarkovMixing.DetailedBalance K π → ∀ t : ℝ, 0 < t →
        relEnt π (measHeat K t μ) ≤
          relEnt π μ * Real.exp (-4 * LogSobolevMC.ChiSquare.logSobolev K π * t)) := by sorry

end LogSobolevMC.Entropy
