-- Prove2me | Theorems.Thm_JohnsonApprox_SetCover_lemma2_selectable_card_le
-- name    : JohnsonApprox.SetCover.lemma2_selectable_card_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:27:44.727322+00:00
-- url     : https://prove2.me/theorems/729de0fa-8bb3-440a-81cc-d7614f2e95c1
-- title:
--   Lemma 2 — a selectable set is at most the sum of the harmonic numbers H(n(K,i)) over any cover M0
-- statement:
--   Let $K$ be any configuration of algorithm C1, and write $n(K, i)$ for $|\mathrm{SET}_K[i]|$, the current size of the $i$-th set. If $M1$ is selectable from $K$ and $M0$ is any set of indices such that $\bigcup_{i \in M0} \mathrm{SET}_K[i] = \mathrm{UNCOV}_K$, then
--   $$|M1| \le \sum_{i \in M0} \left( \sum_{j=1}^{n(K,i)} \frac{1}{j} \right).$$
--
--   This is the heart of the upper bound in Theorem 4: applied to the initial configuration, with $M0$ the index set of an optimal subcover, it bounds the size of every output of C1 by $F^*$ times the harmonic number $H(k)$ when all sets have at most $k$ elements.
--
--   **Formalization Note** The inner sum is Mathlib's `harmonic (n(K,i)) : ℚ`, with $H(0) = 0$. The sizes $n(K, i)$ are those of the configuration $K$, not of the original sets. $M1$ and $M0$ are finite sets of indices of the configuration.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 266, Lemma 2

import Mathlib
import Definitions.Def_JohnsonApprox_SetCover_Problem
import Definitions.Def_JohnsonApprox_SetCover_Config

namespace JohnsonApprox.SetCover

theorem lemma2_selectable_card_le {ι α : Type} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (K : Config ι α) (M1 M0 : Finset ι)
    (h1 : Selectable K M1) (h0 : M0.biUnion K.SET = K.UNCOV) :
    (M1.card : ℚ) ≤ ∑ i ∈ M0, harmonic (K.SET i).card := by sorry

end JohnsonApprox.SetCover
