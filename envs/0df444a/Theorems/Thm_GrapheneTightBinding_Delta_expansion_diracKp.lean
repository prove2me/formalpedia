-- Prove2me | Theorems.Thm_GrapheneTightBinding_Delta_expansion_diracKp
-- name    : GrapheneTightBinding.Delta_expansion_diracKp
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T21:15:45.594981+00:00
-- url     : https://prove2.me/theorems/b09c6a92-e934-4271-ade2-7e034ee9ad11
-- title:
--   Eq. (30): $\Delta_{K'+q}=-ie^{-iK'_xa}\frac{3a}{2}(q_x-iq_y)+o(|q|)$
-- statement:
--   **Linearisation of the structure factor at $K'$ (Eq. 30).** For $a>0$ and $q=k-K'$,
--   $$\Delta_{K'+q} = -i\,e^{-iK'_xa}\,\frac{3a}{2}\,(q_x-iq_y)+o(|q|)\qquad (q\to0).$$
--   The linear form is the complex conjugate of the one at $K$: the two Dirac points carry
--   opposite chirality (valley index), which is the structural reason the two valleys behave
--   as time-reversal partners.
-- source:
--   Franz Utermohlen, Tight-Binding Model for Graphene, lecture notes, September 12, 2018 (Ohio State University); equation numbers as in that text.

import Definitions.Def_graphene_tb_hamiltonian

open Asymptotics Polynomial

namespace GrapheneTightBinding

theorem Delta_expansion_diracKp (a : ℝ) (ha : 0 < a) :
    (fun q : ℝ × ℝ => Delta a (diracKp a + q) -
        (-Complex.I * Complex.exp (-(Complex.I * ((diracKp a).1 * a : ℝ))) *
          (3 * a / 2 : ℝ) * ((q.1 : ℂ) - Complex.I * (q.2 : ℂ))))
      =o[nhds (0 : ℝ × ℝ)] fun q : ℝ × ℝ => euclidNorm q := by
  sorry

end GrapheneTightBinding
