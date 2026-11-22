-- Prove2me | Theorems.Thm_MasulloGRH_expDecayStage_weighted_domination
-- name    : MasulloGRH.expDecayStage_weighted_domination
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T18:50:23.75979+00:00
-- url     : https://prove2.me/theorems/8dd06619-ddb0-4592-9ee1-171e50d946a8
-- title:
--   Interpolation: the weight operators of a stage are dominated by the endpoints
-- statement:
--   Let $G$ be a second-countable, locally compact, Hausdorff abelian group with a surjective module $|\cdot|_G=m\colon G\to\mathbb R_{>0}$, let $I\subseteq\mathbb R$ be a non-empty interval, and let $k$ be a good subgroup. Let $\mathcal S_I(k,G)$ be the space of $k$-invariant elements of $\mathcal S_I(G)$, and for $a\in I$ let $T_a\phi=|\cdot|_G^a\phi$, viewed on $G/k$. Give $\mathcal S(G/k)$ its Schwartz–Bruhat topology. If $a_1\le a\le a_2$ with $a_1,a_2\in I$, then $T_a$ is continuous for the coarsest topology that makes $T_{a_1}$ and $T_{a_2}$ continuous: $$T_a\ \text{is continuous w.r.t.}\ T_{a_1}^{-1}\tau\vee T_{a_2}^{-1}\tau.$$ This is the interpolation Lemma D.3.3.2: $|x|^a\le|x|^{a_1}+|x|^{a_2}$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, Lemma D.3.3.2, Definition D.3.3.3 and Example D.3.3.5 (pp. 804–808)

import Definitions.Def_MasulloGRH_ExpDecayStages

set_option autoImplicit false

universe u

namespace MasulloGRH

theorem expDecayStage_weighted_domination
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (m : G → ℝ) (hm : IsRposModule m)
    (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nonempty) (k : Subgroup G) (hk : IsGoodSubgroup k)
    (a₁ a a₂ : ℝ) (h₁ : a₁ ∈ I) (h₂ : a₂ ∈ I) (hle₁ : a₁ ≤ a) (hle₂ : a ≤ a₂) :
    @Continuous (ExpDecayStage G m I k) (SchwartzBruhat (G ⧸ k))
      (TopologicalSpace.induced (fun y : ExpDecayStage G m I k =>
          ExpDecaySchwartz.weighted k a₁ y.1) inferInstance ⊓
        TopologicalSpace.induced (fun y : ExpDecayStage G m I k =>
          ExpDecaySchwartz.weighted k a₂ y.1) inferInstance) _
      (fun y : ExpDecayStage G m I k => ExpDecaySchwartz.weighted k a y.1) := by
  sorry

end MasulloGRH
