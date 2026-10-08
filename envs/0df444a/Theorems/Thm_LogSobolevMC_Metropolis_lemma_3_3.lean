-- Prove2me | Theorems.Thm_LogSobolevMC_Metropolis_lemma_3_3
-- name    : LogSobolevMC.Metropolis.lemma_3_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:58:59.147342+00:00
-- url     : https://prove2.me/theorems/47e9db22-b4c8-44b0-879b-347a9e33d675
-- title:
--   Lemma 3.3, p. 718 — comparison: ℰ′ ≤ Aℰ and aπ ≤ π′ give λ′ ≤ (A/a)λ and α′ ≤ (A/a)α
-- statement:
--   Let $(K,\pi)$ and $(K',\pi')$ be two Markov chains on the same finite set $\mathcal X$, each with an invariant probability charging every point, with Dirichlet forms $\mathcal E,\mathcal E'$, spectral gaps $\lambda,\lambda'$ and log-Sobolev constants $\alpha,\alpha'$. Assume there are $A,a>0$ with
--
--   $$\mathcal E'(f,f)\le A\,\mathcal E(f,f)\ \text{ for all } f,\qquad a\,\pi(x)\le\pi'(x)\ \text{ for all } x.$$
--
--   Then
--
--   $$\lambda'\le\frac{A}{a}\lambda,\qquad \alpha'\le\frac{A}{a}\alpha.$$
--
--   This comparison principle transfers bounds on the spectral gap and the log-Sobolev constant from a well-understood chain to a less understood one.
--
--   **Formalization Note** No irreducibility is assumed.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 718, Lemma 3.3

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_LogSobolevMC_Metropolis_Setting

namespace LogSobolevMC.Metropolis

/-- Lemma 3.3, p. 718: if two chains `(K, π)`, `(K', π')` on the same finite set satisfy
`ℰ' ≤ Aℰ` and `aπ ≤ π'` with `A, a > 0`, then `λ' ≤ (A/a)λ` and `α' ≤ (A/a)α`. -/
theorem lemma_3_3 {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π) (hπpos : ∀ x, 0 < π x)
    (K' : Matrix V V ℝ) (hK' : MarkovMixing.IsStochastic K')
    (π' : V → ℝ) (hπ' : MarkovMixing.IsStationary K' π') (hπ'pos : ∀ x, 0 < π' x)
    (A a : ℝ) (hA : 0 < A) (ha : 0 < a)
    (hE : ∀ f : V → ℝ, LogSobolevMC.ChiSquare.dirichlet K' π' f f ≤ A * LogSobolevMC.ChiSquare.dirichlet K π f f)
    (hmeas : ∀ x, a * π x ≤ π' x) :
    LogSobolevMC.ChiSquare.gap K' π' ≤ A / a * LogSobolevMC.ChiSquare.gap K π ∧ LogSobolevMC.ChiSquare.logSobolev K' π' ≤ A / a * LogSobolevMC.ChiSquare.logSobolev K π := by sorry

end LogSobolevMC.Metropolis
