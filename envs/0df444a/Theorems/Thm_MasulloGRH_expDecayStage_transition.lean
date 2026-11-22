-- Prove2me | Theorems.Thm_MasulloGRH_expDecayStage_transition
-- name    : MasulloGRH.expDecayStage_transition
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T18:21:46.370809+00:00
-- url     : https://prove2.me/theorems/d072faa4-5090-469c-aa7e-3b64010ff7c5
-- title:
--   Continuity of the transition maps between stages
-- statement:
--   Let $(G,|\cdot|_G)$ be a second countable Hausdorff locally compact abelian group with a surjective module $|\cdot|_G\colon G\to\mathbb R_{>0}$, and let $I\subset\mathbb R$ be a non-empty interval. Write $\mathcal S_I(k,G)$ for the stage of $k$-invariant elements of $\mathcal S_I(G)$, with the projective topology of the maps $T_a\phi=|\cdot|_G^a\phi\in\mathcal S(G/k)$, $a\in I$ (Definition D.3.3.3).
--
--   If $k'\subseteq k$ are good subgroups, then every $k$-invariant element is $k'$-invariant, and the resulting inclusion $\mathcal S_I(k,G)\to\mathcal S_I(k',G)$ is continuous. This holds because pullback along $G/k'\to G/k$ is continuous $\mathcal S(G/k)\to\mathcal S(G/k')$ (the transition maps are topological embeddings, p. 805).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, §D.3.3: Definition D.3.3.3, Example D.3.3.5, Remark D.3.3.8 (pp. 804–807)

import Definitions.Def_MasulloGRH_ExpDecayStages

set_option autoImplicit false

universe u

namespace MasulloGRH

theorem expDecayStage_transition
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (m : G → ℝ) (hm : IsRposModule m)
    (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nonempty) (k k' : Subgroup G)
    (hk : IsGoodSubgroup k) (hk' : IsGoodSubgroup k') (hle : k' ≤ k) :
    ∃ f : ExpDecayStage G m I k → ExpDecayStage G m I k', Continuous f ∧
      ∀ y, ExpDecayStage.incl G m I k' (f y) = ExpDecayStage.incl G m I k y := by
  sorry

end MasulloGRH
