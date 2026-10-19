-- Prove2me | Theorems.Thm_KramersWannier_kw_translation
-- name    : KramersWannier.kw_translation
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-10T13:50:10.591487+00:00
-- url     : https://prove2.me/theorems/e7c41e2a-46dd-4b43-8110-f646f764b959
-- title:
--   Eq. (2.65), Table 1: TD = DT and D† = DT
-- statement:
--   Throughout, $L\ge1$ qubits sit on a ring (site indices mod $L$); basis states are $s\in(\mathbb Z/2)^L$; $X_j|s\rangle=|s+e_j\rangle$, $Z_j|s\rangle=(-1)^{s_j}|s\rangle$, $\eta=\prod_jX_j$, $T|s\rangle=|s'\rangle$ with $s'_k=s_{k-1}$, and $\langle t|\mathsf D|s\rangle=2^{-L/2}(-1)^{\sum_k t_k(s_k+s_{k+1})}$. $T\mathsf D=\mathsf DT$ and $\mathsf D^\dagger=\mathsf DT$.
-- source:
--   N. Seiberg, S. Seifnashri, S.-H. Shao, Non-invertible symmetries and LSM-type constraints on a tensor product Hilbert space, SciPost Phys. 16, 154 (2024), https://arxiv.org/abs/2401.12281, §2.4.1 eq. (2.65) and Table 1 (D̄ = D† = DT)

import Mathlib
import Definitions.Def_KramersWannier_defs

open Matrix

namespace KramersWannier

/-- Eq. (2.65) and Table 1: `TD = DT = D̄`, where `D̄ = D†` is the Hermitian conjugate. -/
theorem kw_translation (L : ℕ) [NeZero L] :
    transl L * kwD L = kwD L * transl L ∧ (kwD L)ᴴ = kwD L * transl L := by sorry

end KramersWannier
