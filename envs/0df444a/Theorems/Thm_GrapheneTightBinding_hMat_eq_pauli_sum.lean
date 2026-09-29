-- Prove2me | Theorems.Thm_GrapheneTightBinding_hMat_eq_pauli_sum
-- name    : GrapheneTightBinding.hMat_eq_pauli_sum
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T20:40:04.136986+00:00
-- url     : https://prove2.me/theorems/87382ca7-3d28-4b1f-bbab-b8b5397160b9
-- title:
--   Eq. (18): $h(k)=-t\sum_\delta[\cos(k\cdot\delta)\sigma_x-\sin(k\cdot\delta)\sigma_y]$
-- statement:
--   **Pauli-matrix form of the Bloch Hamiltonian (Eq. 18).** For all real $a,t$ and every $k$,
--   $$h(k)=-t\sum_{\delta}\bigl[\cos(k\cdot\delta)\,\sigma_x-\sin(k\cdot\delta)\,\sigma_y\bigr],$$
--   the sum running over the three nearest-neighbour vectors. In particular $h(k)$ has no
--   $\sigma_z$ component — the sublattice symmetry of the nearest-neighbour model — which is
--   what makes the $\sigma_z$ mass term of Section 2.3 a genuine deformation.
-- source:
--   Franz Utermohlen, Tight-Binding Model for Graphene, lecture notes, September 12, 2018 (Ohio State University); equation numbers as in that text.

import Definitions.Def_graphene_tb_hamiltonian

open Asymptotics Polynomial

namespace GrapheneTightBinding

theorem hMat_eq_pauli_sum (a t : ℝ) (k : ℝ × ℝ) :
    hMat a t k =
      -(t : ℂ) • ∑ j : Fin 3,
        ((Real.cos (dotp k (nnVec a j)) : ℂ) • pauliX
          - (Real.sin (dotp k (nnVec a j)) : ℂ) • pauliY) := by
  sorry

end GrapheneTightBinding
