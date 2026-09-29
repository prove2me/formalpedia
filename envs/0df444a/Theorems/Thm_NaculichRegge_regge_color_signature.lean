-- Prove2me | Theorems.Thm_NaculichRegge_regge_color_signature
-- name    : NaculichRegge.regge_color_signature
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T23:54:30.536061+00:00
-- url     : https://prove2.me/theorems/f0541da3-ef25-40a5-8f16-d052d9adaa29
-- title:
--   Signature of the Regge colour factors: $P\,C_{ik}=(-1)^{k+1}C_{ik}$
-- statement:
--   For every admissible pair $(i,k)$ (eq. (4.25)), the Regge colour factor $C_{ik}$ has definite signature under the exchange of legs 2 and 3: it is odd when $k$ is even and even when $k$ is odd,
--   $$P\,C_{ik}=(-1)^{k+1}\,C_{ik}.$$
-- source:
--   S. G. Naculich, "All-loop-orders relation between Regge limits of N = 4 SYM and N = 8 supergravity four-point amplitudes", arXiv:2012.00030v2, https://arxiv.org/abs/2012.00030, p. 16, text below eq. (4.23)

import Definitions.Def_NaculichRegge_TraceBasis

open Polynomial

namespace NaculichRegge

/-- Naculich, Sec. 4.4 (below eq. (4.23)): the Regge colour factor `C_{ik}` has signature
`(−1)^{k+1}` under the exchange of legs 2 and 3. -/
theorem regge_color_signature (i k : ℕ) (h : IsReggeIndex i k) :
    crossing.mulVec (reggeColor i k) = ((-1 : ℂ[X]) ^ (k + 1)) • reggeColor i k := by sorry

end NaculichRegge
