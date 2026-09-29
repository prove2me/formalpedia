-- Prove2me | Theorems.Thm_ModularCurve_qExpFrobeniusPullbackModL_qExpFrobeniusPushforwardModL_of_transcendental
-- name    : ModularCurve.qExpFrobeniusPullbackModL_qExpFrobeniusPushforwardModL_of_transcendental
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/f69f64d8-4804-5f99-9f93-31030aab8dcc
-- title:
--   Fr^*Fr_*=ℓ on Pic⁰ in characteristic ℓ
-- statement:
--   Let $\ell$ be a prime, let $K$ be an algebraically closed field of characteristic $\ell$, and let $\Gamma$ be an arbitrary subgroup of $\mathrm{SL}_2(\mathbb{Z})$. Write $F =$ [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) for the intermediate field of the Laurent series field $K((q))$ generated over $K$ by all quotients $\bar p_f/\bar p_g$, where $f,g$ are modular forms of some weight $k$ for the image of $\Gamma$ in $\mathrm{GL}_2(\mathbb{R})$ admitting integral $q$-expansions $p_f,p_g \in \mathbb{Z}[[q]]$ and the reduction of $p_g$ to $K$ is non-zero. Assume `hF`: some $x \in F$ is transcendental over $K$ and $F$ is finite-dimensional over $K(x)$. Let $y$ lie in $\mathrm{Pic}^0(F/K)$, the group of finitely supported $\mathbb{Z}$-valued functions on the places of $F/K$ of total degree zero, modulo those that are divisors of non-zero elements of $F$. Then the composite of the push-forward `qExpFrobeniusPushforwardModL` followed by the pull-back `qExpFrobeniusPullbackModL` along the $\ell$-power Frobenius of $F$ sends $y$ to $\ell \cdot y$. Both maps are defined by a case distinction on the predicate `QExpFrobeniusInputsModL` (existence of principal-divisor data, finiteness along the Frobenius, the fundamental identity and the norm formula), being zero if it fails; the hypothesis `hF` is what makes that predicate available.
--
--   This is the classical statement that, for a function field of one variable over a perfect field of characteristic $\ell$, pull-back after push-forward along the purely inseparable degree-$\ell$ Frobenius acts as multiplication by $\ell$ on the degree-zero divisor class group, here for the $q$-expansion function field of $X(\Gamma)$. It feeds the analysis of the Frobenius endomorphism on Tate modules of modular Jacobians, in particular the results on the quadratic relation satisfied by Frobenius.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpFrobeniusPullbackModL_qExpFrobeniusPushforwardModL_of_transcendental.lean

import Mathlib
import Definitions.Def_ModularCurve_QExpFrobeniusModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.qExpFrobeniusPullbackModL_qExpFrobeniusPushforwardModL_of_transcendental
    (K : Type*) [Field K] [IsAlgClosed K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hF : ∃ x : ModularCurve.qExpFunctionFieldC K Γ, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set (ModularCurve.qExpFunctionFieldC K Γ)))
        (ModularCurve.qExpFunctionFieldC K Γ))
    (y : AlgebraicCurve.Pic0 K (ModularCurve.qExpFunctionFieldC K Γ)) :
    ModularCurve.qExpFrobeniusPullbackModL K Γ ℓ (ModularCurve.qExpFrobeniusPushforwardModL K Γ ℓ y) =
      ℓ • y := by sorry
