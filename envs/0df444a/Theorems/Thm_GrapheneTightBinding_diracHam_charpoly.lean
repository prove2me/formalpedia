-- Prove2me | Theorems.Thm_GrapheneTightBinding_diracHam_charpoly
-- name    : GrapheneTightBinding.diracHam_charpoly
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T21:24:22.901262+00:00
-- url     : https://prove2.me/theorems/dce1bdf3-cf11-4a90-9222-386924488ce2
-- title:
--   Eq. (32): the linearised Hamiltonians have eigenvalues $\pm v_F|q|$
-- statement:
--   **Linear dispersion of the Dirac Hamiltonians (Eq. 32).** For all real $a,t$ and every
--   $q$, both linearised Hamiltonians
--   $$h_K(q)=v_F(q_x\sigma_x-q_y\sigma_y),\qquad h_{K'}(q)=v_F(q_x\sigma_x+q_y\sigma_y),
--   \qquad v_F=\frac{3at}{2},$$
--   have characteristic polynomial $X^2-v_F^2|q|^2$, i.e. eigenvalues
--   $E_\pm(q)=\pm v_F|q|$ with $|q|=\sqrt{q_x^2+q_y^2}$. The dispersion is conical: energy is
--   linear in momentum with slope $v_F$ in every direction, and identical at the two valleys.
-- source:
--   Franz Utermohlen, Tight-Binding Model for Graphene, lecture notes, September 12, 2018 (Ohio State University); equation numbers as in that text.

import Definitions.Def_graphene_tb_hamiltonian

open Asymptotics Polynomial

namespace GrapheneTightBinding

theorem diracHam_charpoly (a t : ℝ) (q : ℝ × ℝ) :
    (diracHamK a t q).charpoly = X ^ 2 - C ((fermiVel a t * euclidNorm q : ℝ) ^ 2 : ℂ) ∧
      (diracHamKp a t q).charpoly = X ^ 2 - C ((fermiVel a t * euclidNorm q : ℝ) ^ 2 : ℂ) := by
  sorry

end GrapheneTightBinding
