-- Prove2me | Theorems.Thm_MarkovMixing_mixing_time_eps
-- name    : MarkovMixing.mixing_time_eps
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T15:16:33.711622+00:00
-- url     : https://prove2.me/theorems/faaa9c68-9992-4868-8f27-1b4326ab02ab
-- title:
--   Section 4.5 -- standard mixing-time inequalities
-- statement:
--   Let $P$ be an irreducible, aperiodic Markov chain on a finite state space $V$ with stationary distribution $\pi$. Write $P^t(x,\cdot)$ for the distribution at time $t$ started at $x$, $\|\mu-\nu\|_{TV}=\max_{A\subseteq V}|\mu(A)-\nu(A)|$ for the total variation distance, and
--   $$d(t)=\max_{x\in V}\bigl\|P^t(x,\cdot)-\pi\bigr\|_{TV}$$
--   for the worst-case distance to stationarity. For a tolerance $\varepsilon$, the **mixing time** is the first time this distance drops to $\varepsilon$,
--   $$t_{\mathrm{mix}}(\varepsilon)=\min\{t\in\mathbb N: d(t)\le\varepsilon\},\qquad t_{\mathrm{mix}}=t_{\mathrm{mix}}(1/4).$$
--
--   The theorem asserts, for any tolerance $0<\varepsilon\le1$, the two standard consequences of submultiplicativity (displays (4.34)–(4.36) of Levin–Peres–Wilmer). First, running the chain for $\ell$ blocks of length $t_{\mathrm{mix}}(\varepsilon)$ shrinks the distance geometrically:
--   $$d\bigl(\ell\cdot t_{\mathrm{mix}}(\varepsilon)\bigr)\le(2\varepsilon)^{\ell}\qquad\text{for every }\ell\in\mathbb N.$$
--   Second, mixing to any tolerance costs only logarithmically many standard mixing times:
--   $$t_{\mathrm{mix}}(\varepsilon)\;\le\;\bigl\lceil\log_2\varepsilon^{-1}\bigr\rceil\;t_{\mathrm{mix}}.$$
--   This is why the convention $\varepsilon=1/4$ is harmless: any other tolerance changes the mixing time by at most a logarithmic factor.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 4.5, Eqs. (4.34)-(4.36), p. 55

import Definitions.Def_mm_mixing
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace MarkovMixing

/-- **§4.5, Eqs. (4.34)–(4.36)** (LPW): for an irreducible aperiodic chain,
`d(ℓ · t_mix(ε)) ≤ (2ε)^ℓ`, and consequently
`t_mix(ε) ≤ ⌈log₂ ε⁻¹⌉ · t_mix`. -/
theorem mixing_time_eps {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : Irreducible P)
    (hap : Aperiodic P) (π : V → ℝ) (hπ : IsStationary P π)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∀ ℓ : ℕ, distStationary P π (ℓ * mixingTime P π ε) ≤ (2 * ε) ^ ℓ) ∧
    mixingTime P π ε ≤ ⌈Real.logb 2 ε⁻¹⌉₊ * tMix P π := by
  sorry

end MarkovMixing
