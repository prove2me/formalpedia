-- Prove2me | Theorems.Thm_Giddings1999_multiparticle_boundary_suppression
-- name    : Giddings1999.multiparticle_boundary_suppression
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T01:51:37.686396+00:00
-- url     : https://prove2.me/theorems/552dc1e1-d498-4a30-b0a6-18920ca61c70
-- title:
--   Eqs. (12), (33): $\Delta_b>\Delta\Rightarrow(\cos r)^{\Delta_b-\Delta}\to0$
-- statement:
--   For real $\Delta<\Delta_b$,
--   $$\lim_{r\to\pi/2^-}(\cos r)^{\Delta_b-\Delta}=0 .$$
--
--   With the spectral assumption (12), $\Delta_b>\Delta$ for every multiparticle state, this is the vanishing of the limit (33). It gives eq. (30): the boundary operators $a_f$ do not connect the vacuum to multiparticle states.
-- source:
--   S. B. Giddings, Boundary S matrix and the anti-de Sitter space to conformal field theory dictionary, Phys. Rev. Lett. 83, 2707 (1999), https://doi.org/10.1103/PhysRevLett.83.2707, eqs. (12), (30), (33), p. 2709

import Mathlib
import Definitions.Def_Giddings1999_AdSModes

open Real Filter Topology

namespace Giddings1999

/-- **Milestone, eqs. (12), (33)**: if `Δ_b > Δ` then `(cos r)^{Δ_b − Δ} → 0` as `r → π/2`. -/
theorem multiparticle_boundary_suppression (Δ Δb : ℝ) (h : Δ < Δb) :
    Tendsto (fun r => cos r ^ (Δb - Δ)) (𝓝[<] (π / 2)) (𝓝 0) := by
  sorry

end Giddings1999
