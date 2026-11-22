-- Prove2me | Theorems.Thm_MasulloGRH_schwartzBruhat_pullback_quotient
-- name    : MasulloGRH.schwartzBruhat_pullback_quotient
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T18:52:53.201446+00:00
-- url     : https://prove2.me/theorems/1bb45c7f-5a4c-457b-835a-05c20f510288
-- title:
--   Pull-back of Schwartz–Bruhat functions along G/k′ → G/k is continuous
-- statement:
--   Let $G$ be a second-countable, locally compact, Hausdorff abelian group, and let $k'\subseteq k$ be good subgroups. Write $p\colon G/k'\to G/k$ for the canonical projection, an open surjection with compact kernel $k/k'$. Then pulling back along $p$ is a continuous linear map of Schwartz–Bruhat spaces:
--   $$p^*\colon\mathcal S(G/k)\to\mathcal S(G/k'),\qquad p^*f=f\circ p.$$
--   This gives functoriality of $\mathcal S$ for quotients by compact subgroups, which yields the transition maps between the stages $\mathcal S_I(k,G)\subseteq\mathcal S_I(k',G)$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, §D.1.5 and §D.3.3

import Definitions.Def_MasulloGRH_LocallyConvex
import Definitions.Def_MasulloGRH_SchwartzBruhat

set_option autoImplicit false

universe u

namespace MasulloGRH

theorem schwartzBruhat_pullback_quotient
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (k k' : Subgroup G)
    (hk : IsGoodSubgroup k) (hk' : IsGoodSubgroup k') (hle : k' ≤ k) :
    ∃ P : SchwartzBruhat (G ⧸ k) →L[ℂ] SchwartzBruhat (G ⧸ k'),
      ∀ (f : SchwartzBruhat (G ⧸ k)) (x : G ⧸ k'),
        (P f).toFun x = f.toFun (QuotientGroup.map k' k (MonoidHom.id G) hle x) := by
  sorry

end MasulloGRH
