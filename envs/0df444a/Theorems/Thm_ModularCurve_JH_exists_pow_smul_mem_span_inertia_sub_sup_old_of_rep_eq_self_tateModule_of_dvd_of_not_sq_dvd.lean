-- Prove2me | Theorems.Thm_ModularCurve_JH_exists_pow_smul_mem_span_inertia_sub_sup_old_of_rep_eq_self_tateModule_of_dvd_of_not_sq_dvd
-- name    : ModularCurve.JH.exists_pow_smul_mem_span_inertia_sub_sup_old_of_rep_eq_self_tateModule_of_dvd_of_not_sq_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/9906b9ec-a91b-50a5-8719-04a974d0c03a
-- title:
--   Inertia-fixed ℓ-adic vectors on J_H(M) are monodromy plus p-old
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $p \mid M$ and $p^2 \nmid M$, let $H \le (\mathbf{Z}/M)^\times$ contain every unit sent to $1$ by the reduction `ZMod.unitsMap` to $(\mathbf{Z}/(M/p))^\times$, with $M/p$ nonzero, and assume the field $F_M =$ `xHFunctionFieldBar M H` (the base change to $\overline{\mathbf{Q}}$ of the $q$-expansion function field of level $M$ and character group $H$, an intermediate field of $\overline{\mathbf{Q}} \subseteq \mathrm{LaurentSeries}(\overline{\mathbf{Q}})$) has principal divisors, i.e. every nonzero $f \in F_M$ has a degree-zero divisor recording its orders at all places. Let $A$ be a valuation subring of $\overline{\mathbf{Q}}$ with $p$ a non-unit of $A$, and let $\ell \neq p$ be a prime. Write $F_{M/p}$ for `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)`, with `infSubgroup` the image of $H$ in $(\mathbf{Z}/(M/p))^\times$, and $J_H =$ `JH` $= \mathrm{Pic}^0$ of the corresponding field over $\overline{\mathbf{Q}}$. The assertion is that there exist two $\overline{\mathbf{Q}}$-algebra maps $\alpha_H, \beta_H \colon F_{M/p} \to F_M$, both integral and making $F_M$ a finite module over the source, and a pair $(\mathrm{apull}_0, \mathrm{apull}_1)$ of additive maps $J_H(M/p) \to J_H(M)$, such that: $\alpha_H$ is the identity on underlying Laurent series; $\beta_H$ is the substitution `qExpand` multiplying Laurent exponents by $p$; $\mathrm{apull}_i$ computes passage to divisor classes of divisor pullback along $\alpha_H$ resp. $\beta_H$, in the sense that $D_v =$ `pullbackAlong` of $D_w$ implies $\mathrm{apull}_i[D_w] = [D_v]$; and, finally, there are $\sigma_0$ in the inertia subgroup of $A$ over $\mathbf{Q}$ inside $\mathrm{Aut}(\overline{\mathbf{Q}}/\mathbf{Q})$ and $k \in \mathbf{N}$ such that every $z$ in the $\ell$-adic Tate module $T_\ell J_H(M)$ (sequences $(z_n)$ with $\ell^n z_n = 0$, $\ell z_{n+1} = z_n$, with the coefficientwise Galois action [`TateModule.rep`](def/EllipticCurve_TateModule.html#L174)) fixed by $\sigma_0$ satisfies $\ell^k z \in S_1 + S_2$, where $S_1$ is the $\mathbf{Z}_\ell$-span of all $\sigma w - w$ with $\sigma$ in that inertia subgroup and $w \in T_\ell J_H(M)$, and $S_2$ is the $\mathbf{Z}_\ell$-span of those $x$ for which there are $w_0, w_1 \in T_\ell J_H(M/p)$ with $x_n = \mathrm{apull}_0((w_0)_n) + \mathrm{apull}_1((w_1)_n)$ for all $n$.
--
--   This packages Grothendieck's description of the $\ell$-adic Tate module of the semistable Jacobian $J_H(M)$ at a prime $p$ exactly dividing the level into the single divisibility statement used later: an inertia-fixed vector is, after multiplication by a bounded power of $\ell$, a sum of monodromy images $\sigma w - w$ and of $p$-old vectors pulled back along the two degeneracy maps. It is invoked in the corresponding statement for $J_1$, from which the level-lowering argument at $p$ proceeds.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JH_exists_pow_smul_mem_span_inertia_sub_sup_old_of_rep_eq_self_tateModule_of_dvd_of_not_sq_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XH
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.JH.exists_pow_smul_mem_span_inertia_sub_sup_old_of_rep_eq_self_tateModule_of_dvd_of_not_sq_dvd
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    ∃ (αH βH : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ]
        ↥(ModularCurve.xHFunctionFieldBar M H))
      (hαint : αH.toRingHom.IsIntegral) (hβint : βH.toRingHom.IsIntegral)
      (hαfin : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) αH) (hβfin : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) βH)
      (αpull : Fin 2 → (ModularCurve.JH (M / p) (ModularCurve.infSubgroup p M H hpM) →+ ModularCurve.JH M H)),

      (∀ u, ((αH u : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        (u : LaurentSeries (AlgebraicClosure ℚ))) ∧
      (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
        ∀ u, ((βH u : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          ModularCurve.qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ))) ∧

      (∀ (Dw : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ)
            (F := ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))))
          (Dv : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H))),
        (Dv : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) =
            AlgebraicCurve.Divisor.pullbackAlong αH hαint
              (Dw : AlgebraicCurve.Divisor (AlgebraicClosure ℚ)
                ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))) →
          αpull 0 (AlgebraicCurve.Pic0.mk Dw) = AlgebraicCurve.Pic0.mk Dv) ∧
      (∀ (Dw : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ)
            (F := ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))))
          (Dv : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H))),
        (Dv : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) =
            AlgebraicCurve.Divisor.pullbackAlong βH hβint
              (Dw : AlgebraicCurve.Divisor (AlgebraicClosure ℚ)
                ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))) →
          αpull 1 (AlgebraicCurve.Pic0.mk Dw) = AlgebraicCurve.Pic0.mk Dv) ∧

      ∃ σ₀ ∈ A.inertiaSubgroupIn ℚ, ∃ k : ℕ,
        ∀ z : TateModule ℓ (ModularCurve.JH M H),
          TateModule.rep ℓ (ModularCurve.JH M H) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ₀ z = z →
          ((ℓ : ℤ_[ℓ]) ^ k) • z ∈
            Submodule.span ℤ_[ℓ]
                {m : TateModule ℓ (ModularCurve.JH M H) |
                  ∃ σ ∈ A.inertiaSubgroupIn ℚ, ∃ w : TateModule ℓ (ModularCurve.JH M H),
                    m = TateModule.rep ℓ (ModularCurve.JH M H)
                          (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ w - w} ⊔
              Submodule.span ℤ_[ℓ]
                {x : TateModule ℓ (ModularCurve.JH M H) |
                  ∃ w₀ w₁ : TateModule ℓ (ModularCurve.JH (M / p) (ModularCurve.infSubgroup p M H hpM)),
                    ∀ n : ℕ, TateModule.proj ℓ (ModularCurve.JH M H) n x =
                        αpull 0 (TateModule.proj ℓ
                          (ModularCurve.JH (M / p) (ModularCurve.infSubgroup p M H hpM)) n w₀) +
                        αpull 1 (TateModule.proj ℓ
                          (ModularCurve.JH (M / p) (ModularCurve.infSubgroup p M H hpM)) n w₁)} := by sorry
