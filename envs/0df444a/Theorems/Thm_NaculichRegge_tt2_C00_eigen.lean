-- Prove2me | Theorems.Thm_NaculichRegge_tt2_C00_eigen
-- name    : NaculichRegge.tt2_C00_eigen
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T23:35:55.692425+00:00
-- url     : https://prove2.me/theorems/0ec02f8e-8490-44ad-b5b6-6350f4ecb64c
-- title:
--   $C_{00}$ is an eigenvector of $\mathbf T_t^2$ with eigenvalue $N$
-- statement:
--   The tree-level $t$-channel colour factor is an eigenvector of the $t$-channel Casimir: $\mathbf T_t^2C_{00}=N\,C_{00}$. In the paper this is $\mathbf T_1\cdot\mathbf T_4C_{00}=-\tfrac12NC_{00}$ (eq. (4.2)) combined with $\mathbf T_t^2=2N+2\mathbf T_1\cdot\mathbf T_4$ (eq. (4.7)); here it is stated for the matrix of eq. (4.15).
-- source:
--   S. G. Naculich, "All-loop-orders relation between Regge limits of N = 4 SYM and N = 8 supergravity four-point amplitudes", arXiv:2012.00030v2, https://arxiv.org/abs/2012.00030, pp. 11–13, eqs. (4.2), (4.7), (4.15)

import Definitions.Def_NaculichRegge_TraceBasis

open Polynomial

namespace NaculichRegge

/-- Naculich, eqs. (4.2), (4.7): `C₀₀` is an eigenvector of `𝐓_t²` with eigenvalue `N`. -/
theorem tt2_C00_eigen : Tt2.mulVec C00 = (X : ℂ[X]) • C00 := by sorry

end NaculichRegge
