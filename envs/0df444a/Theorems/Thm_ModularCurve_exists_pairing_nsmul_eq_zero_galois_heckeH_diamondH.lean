-- Prove2me | Theorems.Thm_ModularCurve_exists_pairing_nsmul_eq_zero_galois_heckeH_diamondH
-- name    : ModularCurve.exists_pairing_nsmul_eq_zero_galois_heckeH_diamondH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/52f06c2b-c473-5751-a6e3-18db445e7767
-- title:
--   Fricke-twisted Weil pairing on J_H(M)[n]
-- statement:
--   Let $M$ be a non-zero natural number, $H$ a subgroup of $(\mathbb{Z}/M)^\times$, and $n$ a non-zero natural number. Write $J_H(M)$ for `JH M H`, the group $\mathrm{Pic}^0$ of the function field `laurentBaseChange (AlgebraicClosure ℚ) (xHFunctionField M H)` over $\overline{\mathbb{Q}}$, that is, degree-zero divisors modulo principal divisors for the subfield of $\overline{\mathbb{Q}}$-Laurent series generated over $\overline{\mathbb{Q}}$ by the image of the level-$\Gamma_H(M)$ $q$-expansion function field over $\mathbb{Q}$. The assertion is that there exists a function $B \colon J_H(M) \times J_H(M) \to \overline{\mathbb{Q}}$, with no condition imposed outside the $n$-torsion, such that for all $x, y, x', y'$ killed by $n$: (i) $B(x,y)^n = 1$; (ii) $B(x+x',y) = B(x,y)B(x',y)$; (iii) $B(x,y+y') = B(x,y)B(x,y')$; (iv) if $B(x,y) = 1$ for every $n$-torsion $y$ then $x = 0$ (left kernel trivial only; nothing is claimed about the right kernel); (v) for every $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and every natural number $c$ coprime to $M$ with $\sigma\zeta = \zeta^{c}$ for all $\zeta$ satisfying $\zeta^M = 1$, one has $B(\langle c\rangle(\sigma x), \sigma y) = \sigma(B(x,y))$, where $\sigma$ acts on $J_H(M)$ through the semilinear action on divisor classes and $\langle c \rangle$ is `diamondHBar M H` at the unit determined by $c$, namely the endomorphism induced by the chosen algebra automorphism `diamondAutHBar M H` (a witness of `IsDiamondAutHBar` if one exists, and the identity otherwise); (vi) for every prime $\ell$ the operator `heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ` is self-adjoint for $B$, this operator being the $\mathrm{Pic}^0$ correspondence attached to the level-$M\ell$ degeneracy maps when `HeckeInputsHAlong` holds and $0$ otherwise; and (vii) every `diamondHBar M H d`, $d \in (\mathbb{Z}/M)^\times$, is self-adjoint for $B$.
--
--   This is the Weil pairing on the $n$-torsion of the Jacobian of $X_H(M)$ composed with the Fricke involution, which normalises $\Gamma_H(M)$ and carries each Hecke correspondence and each diamond operator to its Rosati adjoint; the resulting pairing is therefore Hecke- and diamond-self-adjoint and Galois-equivariant after twisting by a diamond operator. It is the input to the strengthening [`ModularCurve.exists_perfectPairing_nsmul_eq_zero_galois_heckeH_diamondH_forall_addSubgroup_eq_biannihilator`](thm.html#ModularCurve.exists_perfectPairing_nsmul_eq_zero_galois_heckeH_diamondH_forall_addSubgroup_eq_biannihilator), where the pairing is upgraded to a perfect pairing on $J_H(M)[n]$ and subgroups are identified with their biannihilators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_pairing_nsmul_eq_zero_galois_heckeH_diamondH.lean

import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_ModularCurve_ArithmeticGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve in

theorem ModularCurve.exists_pairing_nsmul_eq_zero_galois_heckeH_diamondH
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (n : ℕ) (hn : n ≠ 0) :
    ∃ B : JH M H → JH M H → AlgebraicClosure ℚ,
      (∀ x y : JH M H, n • x = 0 → n • y = 0 → B x y ^ n = 1) ∧
      (∀ x x' y : JH M H, n • x = 0 → n • x' = 0 → n • y = 0 → B (x + x') y = B x y * B x' y) ∧
      (∀ x y y' : JH M H, n • x = 0 → n • y = 0 → n • y' = 0 → B x (y + y') = B x y * B x y') ∧
      (∀ x : JH M H, n • x = 0 → (∀ y : JH M H, n • y = 0 → B x y = 1) → x = 0) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ) (hc : c.Coprime M),
          (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
          ∀ x y : JH M H, n • x = 0 → n • y = 0 →
            B (diamondHBar M H (ZMod.unitOfCoprime c hc) (σ • x)) (σ • y) = σ (B x y)) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (x y : JH M H), n • x = 0 → n • y = 0 →
          haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
          B (heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ x) y =
            B x (heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ y)) ∧
      (∀ (d : (ZMod M)ˣ) (x y : JH M H), n • x = 0 → n • y = 0 →
          B (diamondHBar M H d x) y = B x (diamondHBar M H d y)) := by sorry
