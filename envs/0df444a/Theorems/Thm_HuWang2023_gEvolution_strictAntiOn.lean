-- Prove2me | Theorems.Thm_HuWang2023_gEvolution_strictAntiOn
-- name    : HuWang2023.gEvolution_strictAntiOn
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T00:44:42.978386+00:00
-- url     : https://prove2.me/theorems/bfcad832-fffd-47a5-8894-1e4ed82f1ec4
-- title:
--   Eq. (7): $g(z) = \tilde H_0/(1+z)^\alpha$ is decreasing for $\alpha>0$
-- statement:
--   Let $\tilde H_0 > 0$ and $\alpha>0$. Then the evolution function of Eq. (7),
--   $$g(z) = H_0(z) = \frac{\tilde H_0}{(1+z)^{\alpha}},$$
--   is strictly decreasing on $(-1,\infty)$ (in particular on all physical redshifts $z\ge0$).
--
--   This is the sense in which a positive $\alpha$ describes a descending trend of the inferred $H_0$ with redshift (Section 5).
--
--   **Formalization Note** $(1+z)^\alpha$ is the real power, defined for $1+z>0$.
-- source:
--   Jian-Ping Hu and Fa-Yin Wang, *Hubble Tension: The Evidence of New Physics*, Universe 2023, 9(2), 94, https://doi.org/10.3390/universe9020094, Section 5, p. 13, Eq. (7) and the sentence following it

import Mathlib
import Definitions.Def_HuWang2023_HubbleTension_Defs

namespace HuWang2023

theorem gEvolution_strictAntiOn (H0tilde α : ℝ) (hH : 0 < H0tilde) (hα : 0 < α) :
    StrictAntiOn (gEvolution H0tilde α) (Set.Ioi (-1)) := by sorry

end HuWang2023
