-- Prove2me | Theorems.Thm_ModularCurve_exists_heckeEquivariant_addEquiv_pic0_complex_quotient_periodLattice
-- name    : ModularCurve.exists_heckeEquivariant_addEquiv_pic0_complex_quotient_periodLattice
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/79f6e4e6-85eb-5916-a7a1-08832d6266bc
-- title:
--   Hecke-equivariant Abel–Jacobi isomorphism Pic⁰ ≅ S₂(Γ₀(N))^∨/Λ_N
-- statement:
--   Let $N$ be a nonzero natural number. Assume two hypotheses. First, for every prime $\ell$ the predicate [`ModularCurve.HeckeInputsAlong ℂ N ℓ`](def/ModularCurve_HeckeOperatorTotal.html#L13) holds, i.e. there are integrality data `HeckeAlphaBarIntegral ℂ N ℓ` and `HeckeBetaBarIntegral ℂ N ℓ` for the two maps through level $N\ell$, every nonzero element of the field $\mathbb{C}$-adjoined function field at level $N\ell$ has a degree-zero divisor of its valuations (`HasPrincipalDivisors`), the extension along $\bar\alpha$ is module-finite, and along $\bar\beta$ the fundamental identity and along $\bar\alpha$ the pushforward norm formula hold. Second, [`ModularCurve.PeriodLatticeHeckeStable N`](def/ModularCurve_PeriodLattice.html#L223): for every prime $\ell$ the endomorphism `dualHeckeRep N (heckeGen ℓ)` of $\mathrm{Hom}_{\mathbb C}(S_2(\Gamma_0(N)),\mathbb C)$, the transpose of `cuspHeckeRep N` at the generator $X_\ell$ of `HeckeAlg`, maps `periodLattice N` (the $\mathbb{Z}$-span of the range of `period N`) into itself. Then there is an isomorphism $v$ of additive groups from [`AlgebraicCurve.Pic0 ℂ (laurentBaseChange ℂ (modularFunctionFieldFull N))`](def/AlgebraicCurve_DivisorClassGroup.html#L223), the group of degree-zero divisors modulo principal divisors of the $\mathbb{C}$-constant-field extension inside $\mathbb{C}(\!(q)\!)$ of the modular function field of level $N$, to $\mathrm{Hom}_{\mathbb C}(S_2(\Gamma_0(N)),\mathbb{C})/\Lambda_N$, such that for every prime $\ell$, every class $z$ and every functional $\varphi$ with $v(z) = \varphi \bmod \Lambda_N$, one has $v(T_\ell z) = \mathrm{dualHeckeRep}\,N(X_\ell)(\varphi) \bmod \Lambda_N$, where $T_\ell$ is `heckeOperatorAlong ℂ N ℓ`.
--
--   This is the Abel–Jacobi theorem for the compact Riemann surface $X_0(N)(\mathbb{C})$ — Abel's theorem together with Jacobi inversion — in the form identifying $J_0(N)(\mathbb{C})$ with $S_2(\Gamma_0(N))^\vee/\Lambda_N$, upgraded by Eichler–Shimura compatibility of the algebraic Hecke correspondences with the transposed analytic Hecke operators. It is used to transfer divisibility and injectivity statements about the analytic quotient to the divisor class group, being cited by [`ModularCurve.JZero.divisible`](thm.html#ModularCurve.JZero.divisible) and by [`ModularCurve.exists_injective_heckeEquivariant_addMonoidHom_jZero_pic0_complex`](thm.html#ModularCurve.exists_injective_heckeEquivariant_addMonoidHom_jZero_pic0_complex).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_heckeEquivariant_addEquiv_pic0_complex_quotient_periodLattice.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeOperatorTotal
import Definitions.Def_ModularCurve_PeriodLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_heckeEquivariant_addEquiv_pic0_complex_quotient_periodLattice
    (N : ℕ) [NeZero N]
    (hinC : ∀ ℓ : Nat.Primes,
      haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩; ModularCurve.HeckeInputsAlong ℂ N ℓ)
    (hst : ModularCurve.PeriodLatticeHeckeStable N) :
    ∃ v : AlgebraicCurve.Pic0 ℂ
          (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) ≃+
        (Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) ⧸ ModularCurve.periodLattice N),
      ∀ (ℓ : Nat.Primes)
        (z : AlgebraicCurve.Pic0 ℂ
          (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)))
        (φ : Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)),
        v z = Submodule.Quotient.mk φ →
        v ((haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩; ModularCurve.heckeOperatorAlong ℂ N ℓ) z) =
          Submodule.Quotient.mk (ModularCurve.dualHeckeRep N (ModularCurve.heckeGen ℓ) φ) := by sorry
