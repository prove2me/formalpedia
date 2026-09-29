-- Prove2me | Theorems.Thm_GrapheneTightBinding_bandEnergy_eq
-- name    : GrapheneTightBinding.bandEnergy_eq
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T20:19:40.639897+00:00
-- url     : https://prove2.me/theorems/662e9252-c006-4024-b5c5-e863f58055f7
-- title:
--   Eq. (12): $E_+(k)=t\sqrt{1+4\cos(3k_xa/2)\cos(\sqrt3k_ya/2)+4\cos^2(\sqrt3k_ya/2)}$
-- statement:
--   **The energy bands (Eq. 12).** For a nonnegative hopping amplitude $t$, the upper band
--   energy $E_+(k)=t|\Delta_k|$ is given in closed form by
--   $$E_\pm(k)=\pm t\sqrt{1+4\cos\!\left(\frac{3k_xa}{2}\right)\cos\!\left(\frac{\sqrt3k_ya}{2}\right)
--     +4\cos^2\!\left(\frac{\sqrt3k_ya}{2}\right)} .$$
--   Only the upper branch is stated; the lower branch is its negative.
-- source:
--   Franz Utermohlen, Tight-Binding Model for Graphene, lecture notes, September 12, 2018 (Ohio State University); equation numbers as in that text.

import Definitions.Def_graphene_tb_hamiltonian

open Asymptotics Polynomial

namespace GrapheneTightBinding

theorem bandEnergy_eq (a t : ℝ) (ht : 0 ≤ t) (k : ℝ × ℝ) :
    bandEnergy a t k =
      t * Real.sqrt (1 + 4 * Real.cos (3 * k.1 * a / 2) * Real.cos (Real.sqrt 3 * k.2 * a / 2)
        + 4 * Real.cos (Real.sqrt 3 * k.2 * a / 2) ^ 2) := by
  sorry

end GrapheneTightBinding
