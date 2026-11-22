-- Prove2me | Theorems.Thm_MasulloGRH_exists_countable_rpow_weight_domination
-- name    : MasulloGRH.exists_countable_rpow_weight_domination
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T18:01:00.034606+00:00
-- url     : https://prove2.me/theorems/6a8651f0-b70e-4a12-bbb0-0f5b2866c032
-- title:
--   Countably many exponents dominate all weights $y^a$, $a\in I$
-- statement:
--   Let $I\subseteq\mathbb R$ be a non-empty interval. Then there is a sequence $(a_j)_{j\ge0}$ in $I$ such that for every $x\in I$ there are indices $j,l$ with
--   $$y^{x}\le y^{a_j}+y^{a_l}\qquad\text{for all }y>0.$$
--
--   Applied to $y=|g|_G$ for a module $|\cdot|_G$ on a locally compact abelian group, this shows the following. The family of weights $|\cdot|_G^{a}$, $a\in I$, which defines $\mathcal S_I(G)$ and the projective topologies on its stages $\mathcal S_I(k,G)$ (Masullo, Definitions D.3.3.1 and D.3.3.3), is dominated by the countable subfamily $|\cdot|_G^{a_j}$. This is the countability step that makes those stages metrizable (Lemma D.3.1.2 and Theorem D.3.3.7).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, Lemma D.3.1.2 and Definitions D.3.3.1–D.3.3.3 (pp. 799–805)

import Mathlib

set_option autoImplicit false

namespace MasulloGRH

theorem exists_countable_rpow_weight_domination (I : Set ℝ) (hI : I.OrdConnected)
    (hne : I.Nonempty) :
    ∃ a : ℕ → ℝ, (∀ j, a j ∈ I) ∧
      ∀ x ∈ I, ∃ j l, ∀ y : ℝ, 0 < y → y ^ x ≤ y ^ a j + y ^ a l := by
  sorry

end MasulloGRH
