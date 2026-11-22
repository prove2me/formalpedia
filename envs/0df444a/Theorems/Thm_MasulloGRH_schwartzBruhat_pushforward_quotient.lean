-- Prove2me | Theorems.Thm_MasulloGRH_schwartzBruhat_pushforward_quotient
-- name    : MasulloGRH.schwartzBruhat_pushforward_quotient
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T19:16:24.117524+00:00
-- url     : https://prove2.me/theorems/beaadf04-7288-4fd3-bbd3-4b23e87f4246
-- title:
--   Push-forward of Schwartz–Bruhat functions between quotients by good subgroups is continuous
-- statement:
--   Let $G$ be a second-countable, locally compact, Hausdorff abelian group and $k,k'$ good subgroups. There is a continuous linear map $Q\colon\mathcal S(G/k')\to\mathcal S(G/k)$ given by averaging over $k$:
--   $$(QF)(gk)=\int_k F(gyk')\,dy,$$
--   where $dy$ is the normalized Haar measure of $k$. This is the operator that makes Haar averaging continuous between the stages $\mathcal S_I(k',G)\to\mathcal S_I(k,G)$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, §D.1.5 (proof of Theorem D.1.5.7) and Example D.3.3.5

import Definitions.Def_MasulloGRH_SchwartzBruhatAveraging

set_option autoImplicit false

universe u

namespace MasulloGRH

theorem schwartzBruhat_pushforward_quotient
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (k k' : Subgroup G)
    (hk : IsGoodSubgroup k) (hk' : IsGoodSubgroup k') :
    ∃ Q : SchwartzBruhat (G ⧸ k') →L[ℂ] SchwartzBruhat (G ⧸ k),
      ∀ (F : SchwartzBruhat (G ⧸ k')) (x : G ⧸ k),
        (Q F).toFun x = schwartzBruhatAverage ⊤ k (fun z => F.toFun (QuotientGroup.mk z)) x.out := by
  sorry

end MasulloGRH
