-- Prove2me | Theorems.Thm_GoodmanWitten_eq4_quark_model_matrix_elements
-- name    : GoodmanWitten.eq4_quark_model_matrix_elements
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T12:55:35.086959+00:00
-- url     : https://prove2.me/theorems/ff1c6052-69a6-4fb8-b610-ca2f4278f616
-- title:
--   Eq. (4): nucleon axial matrix elements in the quark model
-- statement:
--   Fix a spin component and write $u_p = \langle p|\bar u\gamma\gamma_5u|p\rangle$, $d_p = \langle p|\bar d\gamma\gamma_5d|p\rangle$, $S_p = \langle p|S|p\rangle$ for the proton and $u_n, d_n, S_n$ for the neutron (real numbers). Assume the isovector relation and the quark-model isosinglet relation for the proton, and their isospin mirrors ($u\leftrightarrow d$, $p\leftrightarrow n$) for the neutron:
--   $$
--   u_p - d_p = 2g_AS_p,\quad u_p + d_p = 2S_p,\quad d_n - u_n = 2g_AS_n,\quad u_n + d_n = 2S_n .
--   $$
--   Then
--   $$
--   u_p = (1+g_A)S_p,\quad d_p = (1-g_A)S_p,\quad u_n = (1-g_A)S_n,\quad d_n = (1+g_A)S_n .
--   $$
--
--   These are the single-nucleon matrix elements from which the nuclear spin-dependent couplings are built.
--
--   **Formalization Note** The paper's "analogous results for neutrons" are encoded as the isospin-mirrored relations for the neutron.
-- source:
--   M. W. Goodman and E. Witten, Detectability of certain dark-matter candidates, Phys. Rev. D 31, 3059-3063 (1985), https://doi.org/10.1103/PhysRevD.31.3059, p. 3061, left column, Eq. (4) and the two displayed relations before it

import Mathlib
import Definitions.Def_GoodmanWitten_basic

namespace GoodmanWitten

theorem eq4_quark_model_matrix_elements (gA uP dP uN dN SP SN : ℝ)
    (hP_isovector : uP - dP = 2 * gA * SP) (hP_isosinglet : uP + dP = 2 * SP)
    (hN_isovector : dN - uN = 2 * gA * SN) (hN_isosinglet : uN + dN = 2 * SN) :
    uP = (1 + gA) * SP ∧ dP = (1 - gA) * SP ∧
      uN = (1 - gA) * SN ∧ dN = (1 + gA) * SN := by sorry

end GoodmanWitten
