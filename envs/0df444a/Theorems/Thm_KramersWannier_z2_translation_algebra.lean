-- Prove2me | Theorems.Thm_KramersWannier_z2_translation_algebra
-- name    : KramersWannier.z2_translation_algebra
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-10T13:47:08.919408+00:00
-- url     : https://prove2.me/theorems/d2f5c306-d430-4bd1-8377-d2a53b951ea8
-- title:
--   Eqs. (1.1)–(1.3), (2.10): invertible symmetries: η² = 1, Tη = ηT, T^L = 1, T shifts Paulis
-- statement:
--   Throughout, $L\ge1$ qubits sit on a ring (site indices mod $L$); basis states are $s\in(\mathbb Z/2)^L$; $X_j|s\rangle=|s+e_j\rangle$, $Z_j|s\rangle=(-1)^{s_j}|s\rangle$, $\eta=\prod_jX_j$, $T|s\rangle=|s'\rangle$ with $s'_k=s_{k-1}$, and $\langle t|\mathsf D|s\rangle=2^{-L/2}(-1)^{\sum_k t_k(s_k+s_{k+1})}$. Then $\eta^2=1$, $T\eta=\eta T$, $T^L=1$, and for every site $j$: $TX_jT^{-1}=X_{j+1}$, $TZ_jT^{-1}=Z_{j+1}$, $\eta X_j=X_j\eta$, $\eta Z_j=-Z_j\eta$.
-- source:
--   N. Seiberg, S. Seifnashri, S.-H. Shao, Non-invertible symmetries and LSM-type constraints on a tensor product Hilbert space, SciPost Phys. 16, 154 (2024), https://arxiv.org/abs/2401.12281, §1.1 eqs. (1.1)–(1.3); §2.1 eq. (2.10); §2.4.1 eq. (2.65)

import Mathlib
import Definitions.Def_KramersWannier_defs

open Matrix

namespace KramersWannier

/-- Eqs. (1.1)–(1.3), (2.10), (2.65): `η² = 1`, `Tη = ηT`, `T^L = 1`, `T X_j T⁻¹ = X_{j+1}`,
`T Z_j T⁻¹ = Z_{j+1}`, `η X_j = X_j η`, `η Z_j = -Z_j η`. -/
theorem z2_translation_algebra (L : ℕ) [NeZero L] :
    eta L * eta L = 1 ∧ transl L * eta L = eta L * transl L ∧ transl L ^ L = 1 ∧
    (∀ j : Fin L, transl L * pauliX L j * (transl L)⁻¹ = pauliX L (j + 1)) ∧
    (∀ j : Fin L, transl L * pauliZ L j * (transl L)⁻¹ = pauliZ L (j + 1)) ∧
    (∀ j : Fin L, eta L * pauliX L j = pauliX L j * eta L) ∧
    (∀ j : Fin L, eta L * pauliZ L j = -(pauliZ L j * eta L)) := by sorry

end KramersWannier
