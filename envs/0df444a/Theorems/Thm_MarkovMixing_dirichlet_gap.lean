-- Prove2me | Theorems.Thm_MarkovMixing_dirichlet_gap
-- name    : MarkovMixing.dirichlet_gap
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T21:46:51.463017+00:00
-- url     : https://prove2.me/theorems/10be0cff-fce3-45a8-b830-ec3678a963ad
-- title:
--   Lemmas 13.11 and 13.12 -- the variational characterization of the gap
-- statement:
--   Let $P$ be an irreducible Markov chain on a finite state space $V$ with at least two states, reversible with respect to its stationary distribution $\pi$ (detailed balance: $\pi(x)P(x,y)=\pi(y)P(y,x)$). Among the eigenvalues of $P$ — the real $\lambda$ admitting a nonzero $f$ with $Pf=\lambda f$ — let $\lambda_2$ be the largest eigenvalue different from $1$, and let $\gamma=1-\lambda_2$ be the **spectral gap**. For functions $f:V\to\mathbb R$ write $\mathbb E_\pi(f)=\sum_xf(x)\pi(x)$ for the mean, $\langle f,f\rangle_\pi=\sum_xf(x)^2\pi(x)$ for the squared $\ell^2(\pi)$-norm, and
--   $$\mathcal E(f)=\frac12\sum_{x,y}\bigl[f(x)-f(y)\bigr]^2\,\pi(x)P(x,y)$$
--   for the **Dirichlet form** — the average squared local variation of $f$ along the chain's transitions.
--
--   The theorem (Lemmas 13.11 and 13.12 of Levin–Peres–Wilmer) asserts:
--
--   1. the spectral gap is the minimal Dirichlet energy over centred unit-norm functions: $\gamma=\inf\bigl\{\mathcal E(f)\;:\;\mathbb E_\pi(f)=0,\ \langle f,f\rangle_\pi=1\bigr\}$;
--   2. the infimum is attained by some such $f$ (an eigenfunction for $\lambda_2$).
--
--   This variational characterization lets one bound the gap from above by exhibiting any single test function, and from below by functional inequalities — the mechanism driving the Cheeger inequality and the comparison method of this mission.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 13.3, Lemmas 13.11-13.12, pp. 175-176

import Definitions.Def_mm_spectral

namespace MarkovMixing

/-- **Lemmas 13.11 and 13.12** (LPW): the spectral gap of a reversible chain
is the minimal Dirichlet energy over functions of mean zero and unit
`ℓ²(π)`-norm, and the minimum is attained. -/
theorem dirichlet_gap {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (hV : 2 ≤ Fintype.card V) (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π) (hrev : DetailedBalance P π) :
    spectralGap P =
      sInf {e : ℝ | ∃ f : V → ℝ, distExp π f = 0 ∧ innerPi π f f = 1 ∧
        e = dirichletForm P π f} ∧
    ∃ f : V → ℝ, distExp π f = 0 ∧ innerPi π f f = 1 ∧
      spectralGap P = dirichletForm P π f := by
  sorry

end MarkovMixing
