-- Prove2me | Theorems.Thm_MarkovMixing_cheeger_inequality
-- name    : MarkovMixing.cheeger_inequality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T21:47:04.046546+00:00
-- url     : https://prove2.me/theorems/ea0ae4b5-e2db-45e1-9b09-680d5e42211f
-- title:
--   Theorem 13.14 -- the Cheeger inequality
-- statement:
--   Let $P$ be an irreducible Markov chain on a finite state space $V$ with at least two states, reversible with respect to its stationary distribution $\pi$ (detailed balance: $\pi(x)P(x,y)=\pi(y)P(y,x)$). Two quantities measure how quickly the chain can move:
--
--   - the **bottleneck constant** $\Phi_\star=\min\bigl\{\Phi(S):\varnothing\ne S\subseteq V,\ \pi(S)\le\tfrac12\bigr\}$, where $\Phi(S)=\sum_{x\in S,\,y\notin S}\pi(x)P(x,y)\,/\,\pi(S)$ is the conditional probability at stationarity of escaping the set $S$ in one step — a geometric, cut-based quantity;
--   - the **spectral gap** $\gamma=1-\lambda_2$, where $\lambda_2$ is the largest eigenvalue of $P$ different from $1$ (an eigenvalue being a real $\lambda$ with $Pf=\lambda f$ for some nonzero $f$) — an analytic quantity.
--
--   The theorem (Theorem 13.14 of Levin–Peres–Wilmer; Jerrum–Sinclair, Lawler–Sokal — the discrete **Cheeger inequality**, capstone of Chapters 12–13) asserts:
--
--   1. $\dfrac{\Phi_\star^2}{2}\;\le\;\gamma$;
--   2. $\gamma\;\le\;2\,\Phi_\star$.
--
--   Bottlenecks and spectral gaps control each other up to a square: a chain mixes rapidly exactly when it has no bottleneck. This equivalence is the backbone of the Markov-chain approach to approximate counting and of expander graph theory.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 13.3, Theorem 13.14, Eq. (13.13), p. 177

import Definitions.Def_mm_spectral

namespace MarkovMixing

/-- **Theorem 13.14** (Jerrum–Sinclair, Lawler–Sokal; LPW), the capstone of
Chapters 12–13: the spectral gap and the bottleneck ratio of a reversible
chain satisfy `Φ⋆²/2 ≤ γ ≤ 2Φ⋆`. -/
theorem cheeger_inequality {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (hV : 2 ≤ Fintype.card V) (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π) (hrev : DetailedBalance P π) :
    bottleneckStar P π ^ 2 / 2 ≤ spectralGap P ∧
    spectralGap P ≤ 2 * bottleneckStar P π := by
  sorry

end MarkovMixing
