-- Prove2me | Theorems.Thm_KramersWannier_kw_intertwines_X
-- name    : KramersWannier.kw_intertwines_X
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-10T13:47:52.760223+00:00
-- url     : https://prove2.me/theorems/6cdfc216-ee9a-434a-8543-768977a5c28f
-- title:
--   Eq. (1.5a): Kramers–Wannier on the field: D X_j = Z_{j-1} Z_j D
-- statement:
--   Throughout, $L\ge1$ qubits sit on a ring (site indices mod $L$); basis states are $s\in(\mathbb Z/2)^L$; $X_j|s\rangle=|s+e_j\rangle$, $Z_j|s\rangle=(-1)^{s_j}|s\rangle$, $\eta=\prod_jX_j$, $T|s\rangle=|s'\rangle$ with $s'_k=s_{k-1}$, and $\langle t|\mathsf D|s\rangle=2^{-L/2}(-1)^{\sum_k t_k(s_k+s_{k+1})}$. For every site $j$, $\mathsf D X_j=Z_{j-1}Z_j\,\mathsf D$.
-- source:
--   N. Seiberg, S. Seifnashri, S.-H. Shao, Non-invertible symmetries and LSM-type constraints on a tensor product Hilbert space, SciPost Phys. 16, 154 (2024), https://arxiv.org/abs/2401.12281, §1.1 eq. (1.5), first line

import Mathlib
import Definitions.Def_KramersWannier_defs

open Matrix

namespace KramersWannier

/-- Eq. (1.5), first line: `D X_j = Z_{j-1} Z_j D` (indices mod `L`). -/
theorem kw_intertwines_X (L : ℕ) [NeZero L] (j : Fin L) :
    kwD L * pauliX L j = pauliZ L (j - 1) * pauliZ L j * kwD L := by sorry

end KramersWannier
