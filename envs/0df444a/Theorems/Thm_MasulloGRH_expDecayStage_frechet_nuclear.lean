-- Prove2me | Theorems.Thm_MasulloGRH_expDecayStage_frechet_nuclear
-- name    : MasulloGRH.expDecayStage_frechet_nuclear
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T18:21:44.752857+00:00
-- url     : https://prove2.me/theorems/0c2871ee-f039-4441-9496-eeb124dfa1d3
-- title:
--   The stages $\mathcal S_I(k,G)$ are nuclear Fréchet
-- statement:
--   Let $(G,|\cdot|_G)$ be a second countable Hausdorff locally compact abelian group with a surjective module $|\cdot|_G\colon G\to\mathbb R_{>0}$, and let $I\subset\mathbb R$ be a non-empty interval. Write $\mathcal S_I(k,G)$ for the stage of $k$-invariant elements of $\mathcal S_I(G)$, with the projective topology of the maps $T_a\phi=|\cdot|_G^a\phi\in\mathcal S(G/k)$, $a\in I$ (Definition D.3.3.3).
--
--   For every good subgroup $k$, the stage $\mathcal S_I(k,G)$ is a nuclear Fréchet space.
--
--   By Example D.3.3.5, $\mathcal S_I(k,G)$ is a closed subspace of a countable product of copies of $\mathcal S(G/k)$. Since $G/k$ is an elementary abelian Lie group, these copies are nuclear Fréchet. Cf. `isFrechet_and_isNuclear_of_countable_projective`, `exists_countable_rpow_weight_domination` and `schwartzBruhat_equiv_elem_of_minimal_goodSubgroup`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, §D.3.3: Definition D.3.3.3, Example D.3.3.5, Remark D.3.3.8 (pp. 804–807)

import Definitions.Def_MasulloGRH_ExpDecayStages

set_option autoImplicit false

universe u

namespace MasulloGRH

theorem expDecayStage_frechet_nuclear
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (m : G → ℝ) (hm : IsRposModule m)
    (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nonempty) (k : Subgroup G) (hk : IsGoodSubgroup k) :
    IsFrechet (ExpDecayStage G m I k) ∧ IsNuclear (ExpDecayStage G m I k) := by
  sorry

end MasulloGRH
