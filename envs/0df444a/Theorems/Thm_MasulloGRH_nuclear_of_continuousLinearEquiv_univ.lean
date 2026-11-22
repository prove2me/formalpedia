-- Prove2me | Theorems.Thm_MasulloGRH_nuclear_of_continuousLinearEquiv_univ
-- name    : MasulloGRH.nuclear_of_continuousLinearEquiv_univ
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T18:27:35.878243+00:00
-- url     : https://prove2.me/theorems/b7fa95b7-4d0d-4789-9eaf-2c7ad88e2130
-- title:
--   Nuclearity transfers along continuous linear isomorphisms between universes
-- statement:
--   If $E\cong F$ are topologically isomorphic complex topological vector spaces (possibly in different universes) and $E$ is nuclear, then $F$ is nuclear.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, §D.3.3 (pp. 804–808)

import Definitions.Def_MasulloGRH_LocallyConvex
import Definitions.Def_MasulloGRH_SchwartzBruhat
import Definitions.Def_MasulloGRH_ExpDecaySpaces

set_option autoImplicit false

universe u v

namespace MasulloGRH

theorem nuclear_of_continuousLinearEquiv_univ (F : Type u) (E : Type v)
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (e : F ≃L[ℂ] E)
    (hE : IsNuclear E) : IsNuclear F := by
  sorry

end MasulloGRH
