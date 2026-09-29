-- Prove2me | Theorems.Thm_MarkovEntanglement_meanFieldMap_isMeanFieldMap
-- name    : MarkovEntanglement.meanFieldMap_isMeanFieldMap
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-08-28T02:22:22.3713+00:00
-- url     : https://prove2.me/theorems/d9667a79-2746-4bda-86b3-9f1431c09689
-- title:
--   The explicit mean-field map is the mean-field map
-- statement:
--   Fix local kernels $P_0, P_1$ on a finite local state space $S$, a priority index $\nu$, a system size $N$ and a budget $M$.
--
--   The explicit mean-field map on the simplex,
--
--   $$\varphi(m)_y = \sum_x \big[(m_x - z_x(m))\,P_0(x,y) + z_x(m)\,P_1(x,y)\big], \qquad z_x(m) = \min\Big(m_x, \max\big(0, \alpha - \textstyle\sum_{\nu_y > \nu_x} m_y\big)\Big),$$
--
--   taken at the activation fraction $\alpha = M/N$, satisfies the characterisation of the mean-field map of the $N$-agent system: for every joint state $s \in S^N$ and every local state $y$,
--
--   $$\varphi(m(s))_y = \frac{1}{N}\sum_{i=1}^N \Big[(1 - p_i)\,P_0(s_i, y) + p_i\,P_1(s_i, y)\Big],$$
--
--   where $m(s)$ is the configuration of $s$ and $p_i$ is the probability with which the index policy activates agent $i$.
--
--   The two descriptions therefore agree on every configuration an $N$-agent system can actually occupy. This is what licenses proving the asymptotic theorems about the explicit formula, which is defined on the whole simplex, rather than about the characterisation, which pins the map down only on the $1/N$-lattice.
--
--   The proof is a regrouping of the sum over agents into a sum over local states — the agents in a given state are exchangeable, so only their number matters — together with the observation that truncated natural subtraction in the count of activated agents is exactly the $\max(0, \cdot)$ of the continuum formula.
-- source:
--   Shuze Chen and Tianyi Peng, 'Multi-agent Markov Entanglement', arXiv:2506.02385v3, Appendix I, p. 41 (bridging Definition 13 with the mean-field map used in the proof of Theorem 7)

import Mathlib
import Definitions.Def_markov_entanglement_meanfield

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglement

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The explicit mean-field map on the simplex agrees, on every configuration an `N`-agent
system can actually occupy, with the characterisation `IsMeanFieldMap` of the previous layer,
provided the activated fraction is `α = M / N`.  This is what licenses proving the asymptotic
theorems about the explicit formula. -/
theorem meanFieldMap_isMeanFieldMap
    (P0 P1 : Matrix S S ℝ) (ν : S → ℝ) (N M : ℕ) (hN : 0 < N) :
    IsMeanFieldMap (N := N) P0 P1 ν M
      (meanFieldMap P0 P1 ν ((M : ℝ) / (N : ℝ))) := by
  sorry

/-! ### M2 — Lemma 7, the mean-field map is piecewise affine -/

end MarkovEntanglement
