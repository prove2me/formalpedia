-- Prove2me | Theorems.Thm_NaculichRegge_crossing_parity_ops
-- name    : NaculichRegge.crossing_parity_ops
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T23:47:56.304951+00:00
-- url     : https://prove2.me/theorems/e55a4d4c-55c4-4b61-936a-5d2423a44fa6
-- title:
--   Crossing parity: $\mathbf T_t^2$ even, $\mathbf T_{s-u}^2$ odd, $C_{00}$ odd
-- statement:
--   Let $P$ be the action of exchanging external legs 2 and 3 on the trace basis ($c[1]\leftrightarrow c[3]$, $c[4]\leftrightarrow c[6]$, $c[2],c[5]$ fixed). Then
--   $$P\,\mathbf T_t^2\,P=\mathbf T_t^2,\qquad P\,\mathbf T_{s-u}^2\,P=-\mathbf T_{s-u}^2,\qquad P\,C_{00}=-C_{00}.$$
-- source:
--   S. G. Naculich, "All-loop-orders relation between Regge limits of N = 4 SYM and N = 8 supergravity four-point amplitudes", arXiv:2012.00030v2, https://arxiv.org/abs/2012.00030, pp. 8, 12–13, eqs. (3.7), (4.7), (4.15)

import Definitions.Def_NaculichRegge_TraceBasis

open Polynomial

namespace NaculichRegge

/-- Naculich, eqs. (3.7), (4.7): under the exchange of legs 2 and 3, `𝐓_t²` is even,
`𝐓_{s-u}²` is odd, and `C₀₀` is odd. -/
theorem crossing_parity_ops :
    crossing * Tt2 * crossing = Tt2 ∧ crossing * Tsu2 * crossing = -Tsu2 ∧
      crossing.mulVec C00 = -C00 := by sorry

end NaculichRegge
