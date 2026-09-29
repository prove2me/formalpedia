-- Prove2me | Theorems.Thm_ModularCurve_qExpFrobeniusPushforwardModL_bijective_of_transcendental
-- name    : ModularCurve.qExpFrobeniusPushforwardModL_bijective_of_transcendental
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/c8b5b9de-1c12-53b5-89c6-78298c8a5fdf
-- title:
--   Bijectivity of the mod-ℓ Frobenius push-forward on Pic⁰
-- statement:
--   Let $K$ be an algebraically closed field, $\ell$ a prime with $K$ of characteristic $\ell$, and let $\Gamma$ be an arbitrary subgroup of $\mathrm{SL}(2,\mathbb{Z})$. Write $\bar F =$ [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) for the intermediate field of the Laurent series field $K((q))$ generated over $K$ by all ratios $\bar p_f/\bar p_g$, where $f,g$ are modular forms of a common weight $k$ for the image of $\Gamma$ in $\mathrm{GL}(2,\mathbb{R})$ having integral $q$-expansions $p_f,p_g\in\mathbb{Z}[[q]]$ and the coefficientwise reduction $\bar p_g$ is nonzero. Assume there is an element $x\in\bar F$ transcendental over $K$ such that $\bar F$ is finite-dimensional over $K(x)$. The conclusion is that the endomorphism [`ModularCurve.qExpFrobeniusPushforwardModL K Γ ℓ`](def/ModularCurve_QExpFrobeniusModL.html#L243) of $\mathrm{Pic}^0$ of $\bar F/K$ — the group of degree-zero divisors modulo the subgroup of principal ones — is bijective. That endomorphism is by definition the map induced on $\mathrm{Pic}^0$ by the degree-zero divisor push-forward along the mod-$\ell$ Frobenius `qExpFrobeniusModL` of $\bar F$ when the package `QExpFrobeniusInputsModL` of inputs (principal divisors, finiteness along the Frobenius, the fundamental identity and the norm formula) holds, and the zero map otherwise; under the stated hypothesis the first branch applies.
--
--   This is the statement that the geometric Frobenius acts bijectively on the degree-zero divisor class group of the $q$-expansion function field of $X(\Gamma)$ in characteristic $\ell$, the divisor-theoretic form of the fact that Frobenius on the Jacobian of a curve over an algebraically closed field is surjective with trivial kernel on classes. It is used downstream in the analysis of Tate modules and of the torsion of the Jacobian of $X_1(N)$ at a prime of good or multiplicative reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpFrobeniusPushforwardModL_bijective_of_transcendental.lean

import Mathlib
import Definitions.Def_ModularCurve_QExpFrobeniusModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.qExpFrobeniusPushforwardModL_bijective_of_transcendental
    (K : Type*) [Field K] [IsAlgClosed K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hF : ∃ x : ModularCurve.qExpFunctionFieldC K Γ, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set (ModularCurve.qExpFunctionFieldC K Γ)))
        (ModularCurve.qExpFunctionFieldC K Γ)) :
    Function.Bijective (ModularCurve.qExpFrobeniusPushforwardModL K Γ ℓ) := by sorry
