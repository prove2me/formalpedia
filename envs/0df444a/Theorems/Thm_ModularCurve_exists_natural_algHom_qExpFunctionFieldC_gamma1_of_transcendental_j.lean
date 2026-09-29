-- Prove2me | Theorems.Thm_ModularCurve_exists_natural_algHom_qExpFunctionFieldC_gamma1_of_transcendental_j
-- name    : ModularCurve.exists_natural_algHom_qExpFunctionFieldC_gamma1_of_transcendental_j
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/87628610-936a-5982-b12e-4cf45e4eddbf
-- title:
--   Galois-equivariant specialisation of X₁(M) functions at (E,P)
-- statement:
--   Let $K$ be an algebraically closed field, $M$ a non-zero natural number with $M \neq 0$ in $K$, and let $F =$ `qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 M)` be the intermediate field of the Laurent series field $K((q))$ generated over $K$ by all quotients $\mathrm{intSeriesC}_K(p_f)/\mathrm{intSeriesC}_K(p_g)$, where $f,g$ are modular forms of one and the same integer weight for $\Gamma_1(M)$ (viewed in $\mathrm{GL}_2(\mathbb{R})$), $p_f,p_g$ are integral power series attached to them by `IsIntegralQExp`, and $\mathrm{intSeriesC}_K(p_g) \neq 0$. Let $x \in F$ be an element whose Laurent series is `jqModC K`, namely $q^{-1}$ times the image in $K[[q]]$ of the integral power series $E_4^3 \cdot \mathrm{dedekindEtaUnitInv}$, i.e. the reduction to $K$ of the $q$-expansion of the modular invariant $j$. Let $k \subseteq \Omega$ be fields forming a scalar tower over $K$, and let $E$ be an elliptic Weierstrass curve over $k$ whose $j$-invariant is transcendental over $K$, and assume that the group of points of $E$ base changed to $\Omega$ killed by $M$ has exactly $M^2$ elements. Then there is a map $\Psi$ assigning to each point $P$ of $E_\Omega$ of exact order $M$ a $K$-algebra homomorphism $\Psi_P \colon F \to \Omega$ with $\Psi_P(x)$ equal to the image of $j(E)$ in $\Omega$, such that $\Psi_{\sigma(P)} = \sigma \circ \Psi_P$ for every $\sigma \in \mathrm{Aut}_k(\Omega)$ and every $P$ of exact order $M$ (where $\sigma$ acts on points coordinatewise), and $\Psi_{-P} = \Psi_P$.
--
--   Classically $\Psi_P$ is evaluation of modular functions of level $\Gamma_1(M)$ at the pair $(E_\Omega, P)$, the transcendence of $j(E)$ placing this pair over the generic point of $Y_1(M)_K$, which is irreducible in every characteristic prime to $M$; the inversion invariance reflects that the diamond operator $-1$ acts trivially on the $j$-line coordinate. It feeds the constructions of Galois extensions of the function fields `qExpFunctionFieldC` of level $\Gamma_H$ with group of order dividing twelve in characteristic two and dividing six in characteristic three.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_natural_algHom_qExpFunctionFieldC_gamma1_of_transcendental_j.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

universe u v in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_natural_algHom_qExpFunctionFieldC_gamma1_of_transcendental_j
    (K : Type u) [Field K] [IsAlgClosed K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0)
    (x : qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 M))
    (hx : (x : LaurentSeries K) = jqModC K)
    (k Ω : Type v) [Field k] [Field Ω] [DecidableEq Ω] [Algebra K k] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower K k Ω] (E : WeierstrassCurve k) [E.IsElliptic]
    (hE : Transcendental K E.j)
    (hfull : Nat.card {P : (E.baseChange Ω).toAffine.Point // M • P = 0} = M ^ 2) :
    ∃ Ψ : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M} →
        {ψ : qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 M) →ₐ[K] Ω // ψ x = algebraMap k Ω E.j},
      (∀ (σ : Ω ≃ₐ[k] Ω) (P P' : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M}),
        P'.1 = WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P.1 →
          ((Ψ P').1 : qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 M) →ₐ[K] Ω) =
            ((σ : Ω →ₐ[k] Ω).restrictScalars K).comp (Ψ P).1) ∧
      (∀ P P' : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M},
        P'.1 = -P.1 → Ψ P' = Ψ P) := by sorry
