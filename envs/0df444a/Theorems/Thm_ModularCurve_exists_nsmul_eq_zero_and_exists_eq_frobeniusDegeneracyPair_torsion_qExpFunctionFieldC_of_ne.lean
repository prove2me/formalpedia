-- Prove2me | Theorems.Thm_ModularCurve_exists_nsmul_eq_zero_and_exists_eq_frobeniusDegeneracyPair_torsion_qExpFunctionFieldC_of_ne
-- name    : ModularCurve.exists_nsmul_eq_zero_and_exists_eq_frobeniusDegeneracyPair_torsion_qExpFunctionFieldC_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/778d03a4-e9bb-5ce8-86f1-4663d9260cec
-- title:
--   Degeneracy pair [[1,F^*],[F^*,⟨ d⟩]] is an ℓ-power-torsion isogeny
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $p$ with $p$ prime, let $N \geq 1$ satisfy $p \nmid N$, and let $H' \leq (\mathbb{Z}/N)^\times$. Write $P = \mathrm{Pic}^0$ of the $q$-expansion function field $\mathtt{qExpFunctionFieldC}\ K\ (\Gamma_{H'}(N))$, i.e. the intermediate field of $K$-Laurent series generated over $K$ by the integral form ratios attached to the congruence subgroup $\Gamma_{H'}(N) = \mathtt{CohCarrier.GammaH}\ N\ H'$, and $\mathrm{Pic}^0$ denoting degree-zero divisors (finitely supported $\mathbb{Z}$-valued functions on places of this field over $K$) modulo principal ones. Given additive endomorphisms $F, F^{-1}, F^*$ of $P$ such that $F$ is the Frobenius pushforward $\mathtt{qExpFrobeniusPushforwardModL}\ K\ (\Gamma_{H'}(N))\ p$ pointwise, $F$ and $F^{-1}$ are mutually inverse, and $F^*z = p \cdot F^{-1}z$ for all $z$; given a unit $d \in (\mathbb{Z}/N)^\times$ and an additive endomorphism $\delta$ of $P$ acting pointwise as the semilinear automorphism $\mathtt{SemilinearAut.ofAlgAut}$ of the diamond algebra automorphism $\mathtt{diamondActionModL}\ K\ N\ H'$ evaluated at a lift $\mathtt{gammaLift}\ N\ d \in \Gamma_0(N)$; and given a prime $\ell \neq p$: there exists $c > 0$ such that, first, for every $n$ and all $z_0, z_1$ killed by $\ell^n$ in $P$ with $z_0 + F^*z_1 = 0$ and $F^*z_0 + \delta z_1 = 0$ one has $c z_0 = 0$ and $c z_1 = 0$; and, second, for every $n$ and all $z_0, z_1$ killed by $\ell^n$ there are $m$ and $y_0, y_1$ killed by $\ell^m$ with $y_0 + F^*y_1 = z_0$ and $F^*y_0 + \delta y_1 = z_1$.
--
--   This is the special-fibre form, on the $\ell$-primary torsion of $\mathrm{Pic}^0$ of $X_{H'}(N)$ in characteristic $p$, of the classical statement that the pair of degeneracy maps $\pi^* + (\pi \circ w_p)^*$ from $J_{H'}(N)^2$ to the Jacobian at level $\Gamma_{H'}(N) \cap \Gamma_0(p)$ is an isogeny onto its image: the matrix $[[1, F^*],[F^*, \langle d \rangle]]$ has finite kernel and is surjective after restriction to $\ell$-power torsion. It feeds the analysis of the Néron-model fibre at $p$, where it is used to separate the toric part of the Tate module of $J_H(Np)$ from the $p$-old part.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_nsmul_eq_zero_and_exists_eq_frobeniusDegeneracyPair_torsion_qExpFunctionFieldC_of_ne.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XHOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_nsmul_eq_zero_and_exists_eq_frobeniusDegeneracyPair_torsion_qExpFunctionFieldC_of_ne
    (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] [IsAlgClosed K]
    (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N) (H' : Subgroup (ZMod N)ˣ)

    (F Finv Fstar : Pic0 K ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H')) →+ Pic0 K ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H')))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL K (CohCarrier.GammaH N H') p z)
    (hFinv : F.comp Finv = AddMonoidHom.id _ ∧ Finv.comp F = AddMonoidHom.id _)
    (hFstar : ∀ z, Fstar z = (p : ℤ) • Finv z)

    (d : (ZMod N)ˣ)
    (δ : Pic0 K ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H')) →+ Pic0 K ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H')))
    (hδ : ∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL K N H' (CuspForm.gammaLift N d)) • z)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    ∃ c : ℕ, 0 < c ∧

      (∀ (n : ℕ) (z₀ z₁ : Pic0 K ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H'))),
        z₀ ∈ Pic0.torsion K ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H')) (ℓ ^ n) →
        z₁ ∈ Pic0.torsion K ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H')) (ℓ ^ n) →
        z₀ + Fstar z₁ = 0 → Fstar z₀ + δ z₁ = 0 → c • z₀ = 0 ∧ c • z₁ = 0) ∧

      (∀ (n : ℕ) (z₀ z₁ : Pic0 K ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H'))),
        z₀ ∈ Pic0.torsion K ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H')) (ℓ ^ n) →
        z₁ ∈ Pic0.torsion K ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H')) (ℓ ^ n) →
        ∃ (m : ℕ) (y₀ y₁ : Pic0 K ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H'))),
          y₀ ∈ Pic0.torsion K ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H')) (ℓ ^ m) ∧
          y₁ ∈ Pic0.torsion K ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H')) (ℓ ^ m) ∧
          y₀ + Fstar y₁ = z₀ ∧ Fstar y₀ + δ y₁ = z₁) := by sorry
