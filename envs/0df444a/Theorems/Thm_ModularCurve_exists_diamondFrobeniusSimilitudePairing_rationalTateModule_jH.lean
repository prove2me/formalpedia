-- Prove2me | Theorems.Thm_ModularCurve_exists_diamondFrobeniusSimilitudePairing_rationalTateModule_jH
-- name    : ModularCurve.exists_diamondFrobeniusSimilitudePairing_rationalTateModule_jH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/4d306af0-00b1-5a48-8c38-2223426f51fd
-- title:
--   Frobenius similitude pairing on the rational Tate module of J_H
-- statement:
--   Fix natural numbers $M$ and $p$ with $M$ nonzero and $p$ prime, and a subgroup $H \le (\mathbb{Z}/M)^\times$. Assume [`ModularCurve.HeckeDiamondInputsHAll M H`](def/ModularCurve_XHOperators.html#L113): for every prime $\ell$ the predicate `HeckeInputsHAlong` holds for $\overline{\mathbb{Q}}$, $M$, $H$, $\ell$, and for every $d \in (\mathbb{Z}/M)^\times$ there is a $\overline{\mathbb{Q}}$-algebra automorphism $\sigma$ of `xHFunctionFieldBar M H` with `IsDiamondAutHBar M H d σ`. Write $J_H$ for the degree-zero divisor class group `JH M H` of `xHFunctionFieldBar M H` over $\overline{\mathbb{Q}}$, $T_p J_H$ for its Tate module (sequences $(x_n)$ in $J_H$ with $p^n x_n = 0$ and $p\,x_{n+1} = x_n$), and $V = \mathbb{Q}_p \otimes_{\mathbb{Z}_p} T_p J_H$. The assertion is that there exists a $\mathbb{Q}_p$-bilinear form $B : V \to V \to \mathbb{Q}_p$ such that: (i) for every prime $\ell$, the endomorphism of $V$ obtained by base change from the action on $T_p J_H$ of the additive endomorphism `heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ` of $J_H$ is self-adjoint for $B$; (ii) likewise the diamond operator `diamondHBar M H d`, the action of the semilinear automorphism attached to `diamondAutHBar M H d`, is self-adjoint for every $d \in (\mathbb{Z}/M)^\times$; (iii) $B(v,v) = 0$ for all $v$; (iv) if $B(v,w) = 0$ for all $w$ then $v = 0$; (v) for every prime $\ell$ with $\ell \nmid M$ and $\ell \ne p$, every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $\ell$ a nonunit of $A$, and every $\sigma \in \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ lying in the decomposition subgroup of $A$ and acting on the residue field of $A$ by $x \mapsto x^\ell$, one has $B(\langle \ell \rangle \sigma x, \sigma y) = \ell\, B(x,y)$ for all $x, y \in V$, where $\sigma$ acts through `JH.tateGaloisRep` and $\langle \ell \rangle$ is the diamond operator at the unit of $\mathbb{Z}/M$ determined by $\ell$.
--
--   Classically $B$ is the Fricke-twisted Weil pairing on the $p$-adic Tate module of the Jacobian $J_H(M)$, with respect to which the Hecke and diamond operators are self-adjoint and Frobenius at a good prime $\ell$ is a similitude with factor $\ell\langle\ell\rangle^{-1}$. It is used to pin down the determinant of the two-dimensional Galois representations cut out of $T_p J_H$, being cited by [`ModularCurve.diamond_mul_coordDet_eq_of_basis_rationalTateModule_jH`](thm.html#ModularCurve.diamond_mul_coordDet_eq_of_basis_rationalTateModule_jH).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_diamondFrobeniusSimilitudePairing_rationalTateModule_jH.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_diamondFrobeniusSimilitudePairing_rationalTateModule_jH
    (M p : ℕ) [NeZero M] [Fact p.Prime] (H : Subgroup (ZMod M)ˣ)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H) :
    ∃ B : TensorProduct ℤ_[p] ℚ_[p] (TateModule p (ModularCurve.JH M H)) →ₗ[ℚ_[p]]
        TensorProduct ℤ_[p] ℚ_[p] (TateModule p (ModularCurve.JH M H)) →ₗ[ℚ_[p]] ℚ_[p],
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime)
          (x y : TensorProduct ℤ_[p] ℚ_[p] (TateModule p (ModularCurve.JH M H))),
        B ((ModularCurve.JH.tateEnd M H p
              (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
                ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ)).baseChange ℚ_[p] x) y =
          B x ((ModularCurve.JH.tateEnd M H p
              (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
                ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ)).baseChange ℚ_[p] y)) ∧
      (∀ (d : (ZMod M)ˣ) (x y : TensorProduct ℤ_[p] ℚ_[p] (TateModule p (ModularCurve.JH M H))),
        B ((ModularCurve.JH.tateEnd M H p (ModularCurve.diamondHBar M H d)).baseChange ℚ_[p] x) y =
          B x ((ModularCurve.JH.tateEnd M H p (ModularCurve.diamondHBar M H d)).baseChange ℚ_[p] y)) ∧
      (∀ v, B v v = 0) ∧
      (∀ v, (∀ w, B v w = 0) → v = 0) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            ∀ x y : TensorProduct ℤ_[p] ℚ_[p] (TateModule p (ModularCurve.JH M H)),
              B ((ModularCurve.JH.tateEnd M H p (ModularCurve.diamondHBar M H
                    (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)))).baseChange
                  ℚ_[p] ((ModularCurve.JH.tateGaloisRep M H p σ).baseChange ℚ_[p] x))
                ((ModularCurve.JH.tateGaloisRep M H p σ).baseChange ℚ_[p] y) =
              (ℓ : ℚ_[p]) * B x y) := by sorry
