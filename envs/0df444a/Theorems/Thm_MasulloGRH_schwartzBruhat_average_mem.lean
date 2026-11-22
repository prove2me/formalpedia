-- Prove2me | Theorems.Thm_MasulloGRH_schwartzBruhat_average_mem
-- name    : MasulloGRH.schwartzBruhat_average_mem
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T19:16:23.931429+00:00
-- url     : https://prove2.me/theorems/48647c18-f7b0-494d-b6a6-29ecf5af745f
-- title:
--   Averaging over a good subgroup preserves Schwartz–Bruhat functions
-- statement:
--   Let $G$ be a second-countable, locally compact, Hausdorff abelian group and $k$ a good (hence compact) subgroup with normalized Haar measure $dy$. For $f\in\mathcal S(G)$,
--   $$A_kf(x)=\int_k f(xy)\,dy\ \in\ \mathcal S(G).$$
--   This averaging operator projects $\mathcal S(G)$ onto its $k$-invariant part.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, §D.1.5 (proof of Theorem D.1.5.7) and Example D.3.3.5

import Definitions.Def_MasulloGRH_SchwartzBruhatAveraging

set_option autoImplicit false

universe u

namespace MasulloGRH

theorem schwartzBruhat_average_mem
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (k : Subgroup G) (hk : IsGoodSubgroup k)
    (f : G → ℂ) (hf : f ∈ schwartzBruhatSubmodule G) :
    schwartzBruhatAverage ⊤ k f ∈ schwartzBruhatSubmodule G := by
  sorry

end MasulloGRH
