-- Prove2me | Theorems.Thm_NoHair_kerr_inner_horizon_geometry
-- name    : NoHair.kerr_inner_horizon_geometry
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T22:54:23.153696+00:00
-- url     : https://prove2.me/theorems/4bca7092-c447-45ab-b05f-ca2172a6d056
-- title:
--   Analytic Kerr geometry on the inner Killing horizon
-- statement:
--   The positive-radius Kerr–Schild metric with $m=5/2$, $a=2$ is real analytic. For $A=\{r>1\}$ the complement is nonempty and the frontier is the connected hypersurface $r=1$. This inner horizon is a nondegenerate Killing horizon. In the usual axial orientation its generator and signed surface gravity are
--   $$\chi=\partial_t+\tfrac25\partial_\varphi,\qquad \kappa_-=-\tfrac3{10}.$$
--   The surface-gravity identity and completeness of the symmetry flow are understood in the mission's sense.
-- source:
--   M. Visser, The Kerr spacetime: A brief introduction, §§5 and 9, equations (32)–(38) and (88)–(94), https://arxiv.org/abs/0706.0622. B. Carter, Global Structure of the Kerr Family of Gravitational Fields, Phys. Rev. 174 (1968) 1559–1571, https://doi.org/10.1103/PhysRev.174.1559.

import Definitions.Def_NoHair_kerrNewman

open NoHair Set
open scoped ContDiff Manifold

theorem NoHair.kerr_inner_horizon_geometry :
    let A := {x : kerrNewmanSpacetime 2 | 1 < ksRadius 2 x.val}
    let g := (kerrNewmanMetricField (5/2) 2 0)
    let F := (kerrNewmanFieldField 2 0)
    IsAnalyticBilinField g ∧ Aᶜ.Nonempty ∧ IsConnected (frontier A) ∧
      IsNondegenerateHorizon g F (frontier A) A := by
  sorry
