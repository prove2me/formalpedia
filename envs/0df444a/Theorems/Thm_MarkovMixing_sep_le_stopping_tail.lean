-- Prove2me | Theorems.Thm_MarkovMixing_sep_le_stopping_tail
-- name    : MarkovMixing.sep_le_stopping_tail
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T20:10:33.740265+00:00
-- url     : https://prove2.me/theorems/cdd11c9a-198c-4ef2-80d9-fba3213b73c9
-- title:
--   Lemma 6.11 -- separation is bounded by the stopping tail
-- statement:
--   Let $P$ be an irreducible Markov chain on a finite state space $V$ with stationary distribution $\pi$, and let $x$ be a starting state. The **separation distance** at time $t$ from $x$ is
--   $$s_x(t)=\max_{y\in V}\Bigl(1-\frac{P^t(x,y)}{\pi(y)}\Bigr),$$
--   which measures how far the time-$t$ distribution is from covering $\pi$ state by state ($s_x(t)=0$ exactly when $P^t(x,y)\ge\pi(y)$ everywhere). A **strong stationary time** $\tau$ for the chain started at $x$ is a randomized stopping rule that stops in finite time almost surely, with the stopped state distributed exactly as $\pi$ and independent of the stopping time.
--
--   The theorem (Lemma 6.11 of Levin–Peres–Wilmer) asserts: for every strong stationary time $\tau$ and every time $t$,
--   $$s_x(t)\;\le\;\mathbb P_x\{\tau>t\}.$$
--   The tail of any strong stationary time controls the separation distance — the reason constructing such times yields mixing upper bounds.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 6.4, Lemma 6.11, p. 79

import Definitions.Def_mm_stopping

namespace MarkovMixing

/-- **Lemma 6.11** (LPW): if `τ` is a strong stationary time for the chain
started at `x`, then the separation distance satisfies
`s_x(t) ≤ P_x{τ > t}`. -/
theorem sep_le_stopping_tail {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π)
    (s : ∀ t : ℕ, (Fin (t + 1) → V) → ℝ) (x : V)
    (hs : IsStrongStationaryTime P π x s) (t : ℕ) :
    sepDist P π x t ≤ stopTailProb P x s t := by
  sorry

end MarkovMixing
