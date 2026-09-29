-- Prove2me | Theorems.Thm_ModularCurve_exists_algHom_qExpFunctionFieldC_gamma1_comp_eq_of_map_eq_or_eq_neg
-- name    : ModularCurve.exists_algHom_qExpFunctionFieldC_gamma1_comp_eq_of_map_eq_or_eq_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/23e53426-b8c0-5943-ad32-e635469e2e1a
-- title:
--   Embedding of the Γ₁(M) q-expansion field fixed by ± P₀
-- statement:
--   Let $K$ be an algebraically closed field, $M$ a nonzero natural number whose image in $K$ is nonzero, and let $F =$ `qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 M)` be the intermediate field of the Laurent series field $K((q))$ obtained by adjoining to $K$ all coefficientwise reductions to $K$ of quotients $p_f/p_g$, where $f$ and $g$ are modular forms of one and the same weight for $\Gamma_1(M)$ (viewed in $\mathrm{GL}_2(\mathbb{R})$), $p_f, p_g$ are integral power series that are $q$-expansions of $f$ and $g$ respectively, and the reduction of $p_g$ is nonzero. Let $x \in F$ be an element whose underlying Laurent series is `jqModC K`, the reduction to $K$ of $q^{-1}\cdot E_4^3\eta^{-24}$, i.e. of the $q$-expansion of the modular invariant $j$. Let $k$ and $\Omega$ be fields with $\Omega$ carrying decidable equality, both $K$-algebras, with $\Omega$ a $k$-algebra forming a scalar tower over $K$ and an algebraic closure of $k$; let $E$ be an elliptic Weierstrass curve over $k$ whose $j$-invariant $E.j$ is transcendental over $K$ and generates $k$ over $K$, i.e. $K(E.j) = k$. Then there exist a point $P_0$ on the affine model of $E$ base-changed to $\Omega$ and a $K$-algebra homomorphism $\psi_0 \colon F \to \Omega$ such that $P_0$ has additive order exactly $M$, $\psi_0(x)$ is the image of $E.j$ in $\Omega$, and every $k$-algebra automorphism $\sigma$ of $\Omega$ whose action on points sends $P_0$ to $P_0$ or to $-P_0$ satisfies $\psi_0$ followed by $\sigma$ (restricted to a $K$-algebra map) $= \psi_0$.
--
--   This is the Kroneckerian-model statement at level $\Gamma_1(M)$: the reduced integral modular functions of level $\Gamma_1(M)$ can be evaluated at the pair consisting of a generic elliptic curve $E$ with transcendental $j$-invariant and a point $P_0$ of exact order $M$, the values landing in the subfield of $\Omega$ fixed by the stabiliser of $\pm P_0$ in $\mathrm{Aut}(\Omega/k)$. It is used by [`ModularCurve.exists_natural_algHom_qExpFunctionFieldC_gamma1_of_transcendental_j`](thm.html#ModularCurve.exists_natural_algHom_qExpFunctionFieldC_gamma1_of_transcendental_j) to obtain the corresponding embedding in a form functorial in the data $(E, P_0)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_algHom_qExpFunctionFieldC_gamma1_comp_eq_of_map_eq_or_eq_neg.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve WeierstrassCurve WeierstrassCurve.Affine

universe u v in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_algHom_qExpFunctionFieldC_gamma1_comp_eq_of_map_eq_or_eq_neg
    (K : Type u) [Field K] [IsAlgClosed K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0)
    (x : qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 M))
    (hx : (x : LaurentSeries K) = jqModC K)
    (k Ω : Type v) [Field k] [Field Ω] [DecidableEq Ω] [Algebra K k] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower K k Ω] [IsAlgClosure k Ω] (E : WeierstrassCurve k) [E.IsElliptic]
    (hE : Transcendental K E.j) (hgen : IntermediateField.adjoin K ({E.j} : Set k) = ⊤) :
    ∃ (P₀ : (E.baseChange Ω).toAffine.Point)
      (ψ₀ : qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 M) →ₐ[K] Ω),
      addOrderOf P₀ = M ∧ ψ₀ x = algebraMap k Ω E.j ∧
      ∀ σ : Ω ≃ₐ[k] Ω,
        (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P₀ = P₀ ∨
          WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P₀ = -P₀) →
        ((σ : Ω →ₐ[k] Ω).restrictScalars K).comp ψ₀ = ψ₀ := by sorry
