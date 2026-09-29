-- Prove2me | Theorems.Thm_ModularCurve_exists_diamondCyclotomicSimilitudePairing_rationalTateModule_jH
-- name    : ModularCurve.exists_diamondCyclotomicSimilitudePairing_rationalTateModule_jH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/044fe761-fa8e-5a5d-906d-ea5547bc12c4
-- title:
--   Fricke-twisted Weil pairing on the rational Tate module of J_H
-- statement:
--   Let $M\ge 1$ and let $p$ be a prime, let $H\le(\mathbb Z/M)^\times$ be a subgroup, and assume [`ModularCurve.HeckeDiamondInputsHAll M H`](def/ModularCurve_XHOperators.html#L113): for every prime $\ell$ the predicate `HeckeInputsHAlong (AlgebraicClosure ℚ) M H ℓ` holds, and for every $d\in(\mathbb Z/M)^\times$ there is an $\overline{\mathbb Q}$-algebra automorphism of `xHFunctionFieldBar M H` satisfying `IsDiamondAutHBar M H d`. Write $J_H=$ `JH M H` for the group of degree-zero divisor classes of that function field modulo principal ones, $T=$ [`TateModule p (JH M H)`](def/EllipticCurve_TateModule.html#L15) for the $\mathbb Z_p$-module of sequences $(x_n)$ in $J_H$ with $p^n x_n=0$ and $p\,x_{n+1}=x_n$, and $V=\mathbb Q_p\otimes_{\mathbb Z_p}T$. Then there is a $\mathbb Q_p$-bilinear form $B:V\times V\to\mathbb Q_p$ such that: (1) for every prime $\ell$, the base change to $\mathbb Q_p$ of the endomorphism of $T$ induced by `heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ` is self-adjoint for $B$; (2) likewise for `diamondHBar M H d` for every $d\in(\mathbb Z/M)^\times$; (3) $B(v,v)=0$ for all $v$; (4) if $B(v,w)=0$ for all $w$ then $v=0$; (5) for every prime $\ell\nmid M$ with $\ell\ne p$, every valuation subring $A$ of $\overline{\mathbb Q}$ with $\ell$ a non-unit of $A$ and every $\sigma\in\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ lying in the decomposition subgroup of $A$ and acting on its residue field by $x\mapsto x^{\ell}$, one has $B(\langle\ell\rangle\sigma x,\sigma y)=\ell\,B(x,y)$, where $\langle\ell\rangle$ is `diamondHBar` at the unit of $\mathbb Z/M$ determined by $\ell$ and $\sigma$ acts through `JH.tateGaloisRep` base changed to $\mathbb Q_p$; and (6) for every $\sigma$ and every $c$ coprime to $M$ with $\sigma\zeta=\zeta^{c}$ for all $\zeta\in\overline{\mathbb Q}$ with $\zeta^{M}=1$, one has $B(\langle c\rangle\sigma x,\sigma y)=\varepsilon_p(\sigma)B(x,y)$, with $\varepsilon_p$ the $p$-adic cyclotomic character viewed in $\mathbb Q_p$.
--
--   This is the Fricke-twisted Weil pairing on the rational $p$-adic Tate module of the Jacobian $J_H(M)$: an alternating nondegenerate form for which the Hecke and diamond operators are self-adjoint and for which the Galois action is a similitude, clause (5) being the Frobenius case of the general similitude law (6). It is used in the analysis of the Tate module in the ordinary case, for instance in the construction of adapted lattice bases on inertia eigenspaces, of the decomposition characters on the multiplicative submodule, and in the relation between Frobenius, $U_\ell$ and the cyclotomic character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_diamondCyclotomicSimilitudePairing_rationalTateModule_jH.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_diamondCyclotomicSimilitudePairing_rationalTateModule_jH
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
              (ℓ : ℚ_[p]) * B x y) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ) (hc : c.Coprime M),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
          ∀ x y : TensorProduct ℤ_[p] ℚ_[p] (TateModule p (ModularCurve.JH M H)),
            B ((ModularCurve.JH.tateEnd M H p (ModularCurve.diamondHBar M H
                  (ZMod.unitOfCoprime c hc))).baseChange ℚ_[p]
                ((ModularCurve.JH.tateGaloisRep M H p σ).baseChange ℚ_[p] x))
              ((ModularCurve.JH.tateGaloisRep M H p σ).baseChange ℚ_[p] y) =
            (((cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) *
              B x y) := by sorry
