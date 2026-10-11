-- Prove2me | Theorems.Thm_KramersWannier_kw_absorbs_eta
-- name    : KramersWannier.kw_absorbs_eta
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-10T13:49:37.860028+00:00
-- url     : https://prove2.me/theorems/31420ce6-f13c-43e1-a1dd-9364b0eb5de9
-- title:
--   Eqs. (1.4), (2.65): D absorbs η: Dη = ηD = D
-- statement:
--   Throughout, $L\ge1$ qubits sit on a ring (site indices mod $L$); basis states are $s\in(\mathbb Z/2)^L$; $X_j|s\rangle=|s+e_j\rangle$, $Z_j|s\rangle=(-1)^{s_j}|s\rangle$, $\eta=\prod_jX_j$, $T|s\rangle=|s'\rangle$ with $s'_k=s_{k-1}$, and $\langle t|\mathsf D|s\rangle=2^{-L/2}(-1)^{\sum_k t_k(s_k+s_{k+1})}$. $\mathsf D\eta=\mathsf D$ and $\eta\mathsf D=\mathsf D$.
-- source:
--   N. Seiberg, S. Seifnashri, S.-H. Shao, Non-invertible symmetries and LSM-type constraints on a tensor product Hilbert space, SciPost Phys. 16, 154 (2024), https://arxiv.org/abs/2401.12281, §1.1 eq. (1.4); §2.4.1 eq. (2.65)

import Mathlib
import Definitions.Def_KramersWannier_defs

open Matrix

namespace KramersWannier

/-- Eqs. (1.4), (2.65): `Dη = ηD = D`. -/
theorem kw_absorbs_eta (L : ℕ) [NeZero L] :
    kwD L * eta L = kwD L ∧ eta L * kwD L = kwD L := by sorry

end KramersWannier
