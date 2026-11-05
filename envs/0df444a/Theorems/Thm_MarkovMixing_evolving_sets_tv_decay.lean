-- Prove2me | Theorems.Thm_MarkovMixing_evolving_sets_tv_decay
-- name    : MarkovMixing.evolving_sets_tv_decay
-- status  : Proved
-- author  : @steven
-- created : 2026-08-22T22:19:14.335345+00:00
-- url     : https://prove2.me/theorems/2f1db001-faf3-442d-8526-fc5ffb23f6d7
-- title:
--   Equation (17.31) — evolving-set total-variation decay
-- statement:
--   Let $P$ be a lazy irreducible Markov chain on a nonempty finite state space with stationary distribution $\pi$. If $d(t)$ is its worst-case total-variation distance, $\pi_{\min}=\min_x\pi(x)$, and $\Phi_\star$ is its bottleneck constant, then for every $t\ge0$,
--   $$d(t)\le \pi_{\min}^{-1}\left(1-\frac{\Phi_\star^2}{2}\right)^t.$$
--   This is Equation (17.31), the quantitative conclusion of the evolving-set supermartingale argument and the immediate input to the Morris–Peres mixing-time theorem.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, Chapter 17, proof of Theorem 17.10, Equation (17.31), p. 253, https://pages.uoregon.edu/dlevin/MARKOV/markovmixing.pdf

import Definitions.Def_mm_martingale

namespace MarkovMixing

/-- **Equation (17.31)** (LPW): for a lazy irreducible finite chain, the evolving-set argument bounds the worst-case total-variation distance geometrically in terms of the bottleneck constant. -/
theorem evolving_sets_tv_decay {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : Irreducible P)
    (hlazy : ∀ x : V, 2⁻¹ ≤ P x x)
    (π : V → ℝ) (hπ : IsStationary P π) :
    ∀ t : ℕ, distStationary P π t ≤
      1 / (⨅ x : V, π x) * (1 - bottleneckStar P π ^ 2 / 2) ^ t := by
  sorry

end MarkovMixing
