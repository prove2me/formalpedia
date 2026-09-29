-- Prove2me | Theorems.Thm_ModularCurve_heckeOperatorHAlong_diamondHBar_comm
-- name    : ModularCurve.heckeOperatorHAlong_diamondHBar_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/64c94d9b-9a74-52c3-bd05-8c3c8a00e0bd
-- title:
--   Hecke operators on J_H(M) commute with diamond operators
-- statement:
--   Fix an integer $M \neq 0$, a subgroup $H \leq (\mathbb{Z}/M)^{\times}$, a prime $\ell$, a unit $d \in (\mathbb{Z}/M)^{\times}$, and a point $P$ of [`ModularCurve.JH M H`](def/ModularCurve_XH.html#L127), the group $\mathrm{Pic}^{0}$ of degree-zero divisor classes modulo principal divisors of the intermediate field `laurentBaseChange (AlgebraicClosure ℚ) (xHFunctionField M H)`, that is, of the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of the function field `xHFunctionField M H` $\subseteq \mathbb{Q}((q))$ of $X_H(M)$. Two additive endomorphisms of this group are compared. The first, `heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ`, is by definition the divisor-class correspondence $\mathrm{Pic}^{0}$-`correspondence` built from the two maps `heckeBetaHBar` and `heckeAlphaHBar` together with the integrality, fundamental-identity, finiteness and norm-formula data packaged in the predicate `HeckeInputsHAlong (AlgebraicClosure ℚ) M H ℓ`, and is the zero endomorphism when that predicate fails. The second, `diamondHBar M H d`, is the action on divisor classes of the semilinear automorphism attached to `diamondAutHBar M H d`, the chosen $\overline{\mathbb{Q}}$-automorphism of the base-changed function field satisfying `IsDiamondAutHBar M H d` if one exists, and the identity otherwise. The assertion is that the two endomorphisms commute at $P$: applying the Hecke operator to $\langle d\rangle P$ gives the same class as applying $\langle d\rangle$ to the Hecke image of $P$. Primality of $\ell$ enters only through $\ell \neq 0$.
--
--   This is the commutation of the covariant Hecke correspondence $T_\ell$ (or $U_\ell$ when $\ell \mid M$) with the diamond operator $\langle d\rangle$ on the Jacobian of $X_H(M)$ over $\overline{\mathbb{Q}}$, the divisor-class form of Diamond–Shurman Proposition 5.2.4(a). It underlies the commutativity of the Hecke algebra acting on $J_H(M)$ and is used in the construction of Galois-stable Hecke lattices in the torsion of $J_H$ and in the Eichler–Shimura style relations at full level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeOperatorHAlong_diamondHBar_comm.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.heckeOperatorHAlong_diamondHBar_comm (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [Fact ℓ.Prime] (d : (ZMod M)ˣ) (P : ModularCurve.JH M H) :
    ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ (ModularCurve.diamondHBar M H d P) =
      ModularCurve.diamondHBar M H d
        (ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ P) := by sorry
