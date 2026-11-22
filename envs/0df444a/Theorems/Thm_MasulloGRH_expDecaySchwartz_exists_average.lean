-- Prove2me | Theorems.Thm_MasulloGRH_expDecaySchwartz_exists_average
-- name    : MasulloGRH.expDecaySchwartz_exists_average
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T18:57:30.264196+00:00
-- url     : https://prove2.me/theorems/d10fd061-41f0-4cab-9e05-856a948106e9
-- title:
--   Haar averaging over a good subgroup maps S_I(G) onto a stage, continuously on each stage
-- statement:
--   Let $G$ be a second-countable, locally compact, Hausdorff abelian group with a surjective module $|\cdot|_G\colon G\to\mathbb R_{>0}$. Let $I$ be a non-empty interval and $k$ a good (hence compact) subgroup with normalized Haar measure $dh$. The averaging operator
--   $$A\phi(g)=\int_k\phi(gh)\,dh$$
--   maps $\mathcal S_I(G)$ linearly onto the stage $\mathcal S_I(k,G)$ of $k$-invariant elements and fixes that stage. For every good subgroup $k'$, its restriction $\mathcal S_I(k',G)\to\mathcal S_I(k,G)$ is continuous for the stage topologies. This is the averaging step of Example D.3.3.5. Together with the inductive-limit topology of $\mathcal S_I(G)$, it makes $\mathcal S_I(k,G)$ a continuous retract.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, Example D.3.3.5 (pp. 804–808)

import Definitions.Def_MasulloGRH_ExpDecayStages

set_option autoImplicit false

universe u

namespace MasulloGRH

theorem expDecaySchwartz_exists_average
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (m : G → ℝ) (hm : IsRposModule m)
    (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nonempty) (k : Subgroup G) (hk : IsGoodSubgroup k) :
    ∃ A : ExpDecaySchwartz G m I →ₗ[ℂ] ExpDecayStage G m I k,
      (∀ y, A (ExpDecayStage.incl G m I k y) = y) ∧
      ∀ k' : Subgroup G, IsGoodSubgroup k' →
        Continuous (fun y : ExpDecayStage G m I k' => A (ExpDecayStage.incl G m I k' y)) := by
  sorry

end MasulloGRH
