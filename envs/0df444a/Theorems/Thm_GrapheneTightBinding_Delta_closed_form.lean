-- Prove2me | Theorems.Thm_GrapheneTightBinding_Delta_closed_form
-- name    : GrapheneTightBinding.Delta_closed_form
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T20:08:26.230406+00:00
-- url     : https://prove2.me/theorems/02934bc7-07c1-4374-92a3-4a6abf64accc
-- title:
--   Eq. (11): $\Delta_k = e^{-ik_xa}[1+2e^{i3k_xa/2}\cos(\sqrt3k_ya/2)]$
-- statement:
--   **Closed form of the structure factor (Eq. 11).** For every lattice constant
--   $a\in\mathbb{R}$ and every wave vector $k=(k_x,k_y)\in\mathbb{R}^2$, the sum over the
--   three nearest-neighbour vectors factorises as
--   $$\Delta_k \;=\; \sum_{j=1}^{3} e^{i k\cdot\delta_j}
--     \;=\; e^{-i k_x a}\left[\,1+2\,e^{i 3 k_x a/2}\cos\!\left(\frac{\sqrt3\,k_y a}{2}\right)\right].$$
--   This is the first step of the source's computation of the band energies: it isolates the
--   overall phase $e^{-ik_xa}$ coming from $\delta_3$ and combines the $\delta_1,\delta_2$
--   terms into a cosine.
-- source:
--   Franz Utermohlen, Tight-Binding Model for Graphene, lecture notes, September 12, 2018 (Ohio State University); equation numbers as in that text.

import Definitions.Def_graphene_tb_hamiltonian

open Asymptotics Polynomial

namespace GrapheneTightBinding

theorem Delta_closed_form (a : ℝ) (k : ℝ × ℝ) :
    Delta a k =
      Complex.exp (-(Complex.I * (k.1 * a : ℝ))) *
        (1 + 2 * Complex.exp (Complex.I * (3 * k.1 * a / 2 : ℝ)) *
          (Real.cos (Real.sqrt 3 * k.2 * a / 2) : ℂ)) := by
  sorry

end GrapheneTightBinding
