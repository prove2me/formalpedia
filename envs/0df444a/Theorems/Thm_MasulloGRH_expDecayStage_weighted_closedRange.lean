-- Prove2me | Theorems.Thm_MasulloGRH_expDecayStage_weighted_closedRange
-- name    : MasulloGRH.expDecayStage_weighted_closedRange
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T18:50:11.518864+00:00
-- url     : https://prove2.me/theorems/a673b686-641a-4bd4-91eb-891343a04e49
-- title:
--   The weight embedding of a stage has closed image
-- statement:
--   Let $G$ be a second-countable, locally compact, Hausdorff abelian group with a surjective module $|\cdot|_G=m\colon G\to\mathbb R_{>0}$, let $I\subseteq\mathbb R$ be a non-empty interval, and let $k$ be a good subgroup. Let $\mathcal S_I(k,G)$ be the space of $k$-invariant elements of $\mathcal S_I(G)$, and for $a\in I$ let $T_a\phi=|\cdot|_G^a\phi$, viewed on $G/k$. Let $J\subseteq I$ be such that every $a\in I$ lies between two elements of $J$. Then the image of $$\mathcal S_I(k,G)\to\prod_{j\in J}\mathcal S(G/k),\quad\phi\mapsto(T_j\phi)_j$$ is closed (Example D.3.3.5). Formalization note: the index is lifted to the universe of $G$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, Lemma D.3.3.2, Definition D.3.3.3 and Example D.3.3.5 (pp. 804–808)

import Definitions.Def_MasulloGRH_ExpDecayStages

set_option autoImplicit false

universe u

namespace MasulloGRH

theorem expDecayStage_weighted_closedRange
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (m : G → ℝ) (hm : IsRposModule m)
    (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nonempty) (k : Subgroup G) (hk : IsGoodSubgroup k)
    (J : Set ℝ) (hJ : J ⊆ I) (hbet : ∀ a ∈ I, ∃ a₁ ∈ J, ∃ a₂ ∈ J, a₁ ≤ a ∧ a ≤ a₂) :
    IsClosed (Set.range fun (y : ExpDecayStage G m I k) (j : ULift.{u} J) =>
      ExpDecaySchwartz.weighted k (j.down : ℝ) y.1) := by
  sorry

end MasulloGRH
