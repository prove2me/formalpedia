-- Prove2me | Theorems.Thm_MasulloGRH_expDecayStage_weighted_mem
-- name    : MasulloGRH.expDecayStage_weighted_mem
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T18:50:58.279801+00:00
-- url     : https://prove2.me/theorems/6274cfdc-9c38-4960-b475-98a8939119f9
-- title:
--   The weighted functions of a stage are Schwartz–Bruhat on G/k
-- statement:
--   Let $G$ be a second-countable, locally compact, Hausdorff abelian group with a surjective module $|\cdot|_G=m\colon G\to\mathbb R_{>0}$, let $I\subseteq\mathbb R$ be a non-empty interval, and let $k$ be a good subgroup. Let $\mathcal S_I(k,G)$ be the space of $k$-invariant elements of $\mathcal S_I(G)$, and for $a\in I$ let $T_a\phi=|\cdot|_G^a\phi$, viewed on $G/k$. Then for every $\phi\in\mathcal S_I(k,G)$ and $a\in I$, $$T_a\phi\in\mathcal S(G/k).$$ So the operators $T_a$ are well defined (and linear) on the stage.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, Lemma D.3.3.2, Definition D.3.3.3 and Example D.3.3.5 (pp. 804–808)

import Definitions.Def_MasulloGRH_ExpDecayStages

set_option autoImplicit false

universe u

namespace MasulloGRH

theorem expDecayStage_weighted_mem
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (m : G → ℝ) (hm : IsRposModule m)
    (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nonempty) (k : Subgroup G) (hk : IsGoodSubgroup k)
    (y : ExpDecayStage G m I k) (a : ℝ) (ha : a ∈ I) :
    (fun x : G ⧸ k => ((m x.out ^ a : ℝ) : ℂ) * y.1.toFun x.out) ∈
      schwartzBruhatSubmodule (G ⧸ k) := by
  sorry

end MasulloGRH
