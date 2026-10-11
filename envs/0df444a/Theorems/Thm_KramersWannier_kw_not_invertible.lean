-- Prove2me | Theorems.Thm_KramersWannier_kw_not_invertible
-- name    : KramersWannier.kw_not_invertible
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-10T13:50:38.914161+00:00
-- url     : https://prove2.me/theorems/447ffe83-af48-432e-b023-f274eac7eb4a
-- title:
--   §1.1 (below eq. (1.4)): D is not invertible
-- statement:
--   Throughout, $L\ge1$ qubits sit on a ring (site indices mod $L$); basis states are $s\in(\mathbb Z/2)^L$; $X_j|s\rangle=|s+e_j\rangle$, $Z_j|s\rangle=(-1)^{s_j}|s\rangle$, $\eta=\prod_jX_j$, $T|s\rangle=|s'\rangle$ with $s'_k=s_{k-1}$, and $\langle t|\mathsf D|s\rangle=2^{-L/2}(-1)^{\sum_k t_k(s_k+s_{k+1})}$. $\mathsf D$ is not a unit of the matrix ring, and there is a nonzero vector $v$ with $\mathsf Dv=0$.
-- source:
--   N. Seiberg, S. Seifnashri, S.-H. Shao, Non-invertible symmetries and LSM-type constraints on a tensor product Hilbert space, SciPost Phys. 16, 154 (2024), https://arxiv.org/abs/2401.12281, §1.1, text below eq. (1.4)

import Mathlib
import Definitions.Def_KramersWannier_defs

open Matrix

namespace KramersWannier

/-- §1.1, below eq. (1.4): `D` is not invertible; it has a nontrivial kernel. -/
theorem kw_not_invertible (L : ℕ) [NeZero L] :
    ¬ IsUnit (kwD L) ∧ ∃ v : Config L → ℂ, v ≠ 0 ∧ kwD L *ᵥ v = 0 := by sorry

end KramersWannier
