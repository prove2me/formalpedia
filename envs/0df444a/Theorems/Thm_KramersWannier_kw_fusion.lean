-- Prove2me | Theorems.Thm_KramersWannier_kw_fusion
-- name    : KramersWannier.kw_fusion
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-10T13:51:15.793972+00:00
-- url     : https://prove2.me/theorems/64c4ec9f-9965-4081-bb59-e5d8aadafcce
-- title:
--   Eqs. (1.4), (2.65): fusion rule D² = (1 + η) T⁻¹
-- statement:
--   Throughout, $L\ge1$ qubits sit on a ring (site indices mod $L$); basis states are $s\in(\mathbb Z/2)^L$; $X_j|s\rangle=|s+e_j\rangle$, $Z_j|s\rangle=(-1)^{s_j}|s\rangle$, $\eta=\prod_jX_j$, $T|s\rangle=|s'\rangle$ with $s'_k=s_{k-1}$, and $\langle t|\mathsf D|s\rangle=2^{-L/2}(-1)^{\sum_k t_k(s_k+s_{k+1})}$. For every $L\ge1$: $\mathsf D^2=(1+\eta)\,T^{-1}$.
-- source:
--   N. Seiberg, S. Seifnashri, S.-H. Shao, Non-invertible symmetries and LSM-type constraints on a tensor product Hilbert space, SciPost Phys. 16, 154 (2024), https://arxiv.org/abs/2401.12281, §1.1 eq. (1.4); §2.4.1 eq. (2.65); App. F eq. (F.18)

import Mathlib
import Definitions.Def_KramersWannier_defs

open Matrix

namespace KramersWannier

/-- Eqs. (1.4), (2.65), (F.18): the non-invertible fusion rule `D² = (1 + η) T⁻¹`. -/
theorem kw_fusion (L : ℕ) [NeZero L] :
    kwD L * kwD L = (1 + eta L) * (transl L)⁻¹ := by sorry

end KramersWannier
