-- Prove2me | Theorems.Thm_KramersWannier_kw_intertwines_ZZ
-- name    : KramersWannier.kw_intertwines_ZZ
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-10T13:48:34.879817+00:00
-- url     : https://prove2.me/theorems/00c7de31-0c09-48d5-b97c-463ca3c8e92c
-- title:
--   Eq. (1.5b): Kramers–Wannier on the coupling: D Z_{j-1} Z_j = X_{j-1} D
-- statement:
--   Throughout, $L\ge1$ qubits sit on a ring (site indices mod $L$); basis states are $s\in(\mathbb Z/2)^L$; $X_j|s\rangle=|s+e_j\rangle$, $Z_j|s\rangle=(-1)^{s_j}|s\rangle$, $\eta=\prod_jX_j$, $T|s\rangle=|s'\rangle$ with $s'_k=s_{k-1}$, and $\langle t|\mathsf D|s\rangle=2^{-L/2}(-1)^{\sum_k t_k(s_k+s_{k+1})}$. For every site $j$, $\mathsf D Z_{j-1}Z_j=X_{j-1}\,\mathsf D$.
-- source:
--   N. Seiberg, S. Seifnashri, S.-H. Shao, Non-invertible symmetries and LSM-type constraints on a tensor product Hilbert space, SciPost Phys. 16, 154 (2024), https://arxiv.org/abs/2401.12281, §1.1 eq. (1.5), second line

import Mathlib
import Definitions.Def_KramersWannier_defs

open Matrix

namespace KramersWannier

/-- Eq. (1.5), second line: `D Z_{j-1} Z_j = X_{j-1} D` (indices mod `L`). -/
theorem kw_intertwines_ZZ (L : ℕ) [NeZero L] (j : Fin L) :
    kwD L * (pauliZ L (j - 1) * pauliZ L j) = pauliX L (j - 1) * kwD L := by sorry

end KramersWannier
