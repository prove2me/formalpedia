-- Prove2me | Theorems.Thm_GrapheneTightBinding_Delta_expansion_diracK
-- name    : GrapheneTightBinding.Delta_expansion_diracK
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T21:01:12.400981+00:00
-- url     : https://prove2.me/theorems/0f886d47-0d5e-4047-aa21-fe291e5b03e8
-- title:
--   Eqs. (22)–(23): $\Delta_{K+q}=-ie^{-iK_xa}\frac{3a}{2}(q_x+iq_y)+o(|q|)$
-- statement:
--   **Linearisation of the structure factor at $K$ (Eqs. 22–23).** For $a>0$, writing
--   $q=k-K$ for the momentum measured from the Dirac point,
--   $$\Delta_{K+q} = -i\,e^{-iK_xa}\,\frac{3a}{2}\,(q_x+iq_y)+o(|q|)\qquad (q\to0),$$
--   with $|q|=\sqrt{q_x^2+q_y^2}$. Up to the constant phase $-ie^{-iK_xa}$ — which does not
--   affect the energies, since $E_\pm=\pm t|\Delta_k|$ — this is Eq. (24),
--   $\Delta_{K+q}=-\tfrac{3a}{2}(q_x+iq_y)$, the chiral linear form responsible for the Dirac
--   cone at $K$.
-- source:
--   Franz Utermohlen, Tight-Binding Model for Graphene, lecture notes, September 12, 2018 (Ohio State University); equation numbers as in that text.

import Definitions.Def_graphene_tb_hamiltonian

open Asymptotics Polynomial

namespace GrapheneTightBinding

theorem Delta_expansion_diracK (a : ℝ) (ha : 0 < a) :
    (fun q : ℝ × ℝ => Delta a (diracK a + q) -
        (-Complex.I * Complex.exp (-(Complex.I * ((diracK a).1 * a : ℝ))) *
          (3 * a / 2 : ℝ) * ((q.1 : ℂ) + Complex.I * (q.2 : ℂ))))
      =o[nhds (0 : ℝ × ℝ)] fun q : ℝ × ℝ => euclidNorm q := by
  sorry

end GrapheneTightBinding
