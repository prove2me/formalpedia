-- Prove2me | Theorems.Thm_ModularCurve_exists_natural_diamond_algHom_qExpFunctionFieldC_gammaH_bot_of_transcendental_j
-- name    : ModularCurve.exists_natural_diamond_algHom_qExpFunctionFieldC_gammaH_bot_of_transcendental_j
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/527bab60-5cd9-5fab-b9b2-9f993e1b0b1a
-- title:
--   Diamond-equivariant moduli embeddings for X₁(M) at transcendental j
-- statement:
--   Let $K$ be an algebraically closed field and $M$ a nonzero natural number with $M \neq 0$ in $K$. Write $F$ for `qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)`, the subfield of the Laurent series field $K((q))$ generated over $K$ by all quotients $\bar p_f/\bar p_g$, where $f,g$ are modular forms of one and the same weight for the subgroup of $\mathrm{SL}(2,\mathbb{Z})$ consisting of those elements of $\Gamma_0(M)$ whose image under `gamma0Units M` is trivial (lower right entry $\equiv 1 \bmod M$), $p_f,p_g$ are integral power series whose images over $\mathbb{C}$ are the $q$-expansions of $f,g$, and the reduction $\bar p_g$ of $p_g$ to $K$ is nonzero. Let $x \in F$ be an element whose Laurent series is `jqModC K`, the reduction to $K$ of $q^{-1}\cdot$`jNum`, i.e. of the $q$-expansion of $j$. Let $k \subseteq \Omega$ be extension fields of $K$ forming a scalar tower over $K$, and let $E$ be an elliptic Weierstrass curve over $k$ whose $j$-invariant is transcendental over $K$ and such that the set of points of $E$ base-changed to $\Omega$ killed by $M$ has exactly $M^2$ elements. Then there is an assignment $\Psi$ attaching to every point $P$ of exact additive order $M$ in $(E_\Omega)(\Omega)$ a $K$-algebra homomorphism $\Psi_P \colon F \to \Omega$ with $\Psi_P(x) =$ the image of $j(E)$ in $\Omega$, such that: (i) for every $k$-algebra automorphism $\sigma$ of $\Omega$ and points $P,P'$ of order $M$ with $P'$ the image of $P$ under $\sigma$, one has $\Psi_{P'} = \sigma \circ \Psi_P$; (ii) for every monoid homomorphism $\rho$ from $\Gamma_0(M)$ to the $K$-algebra automorphisms of $F$ satisfying `IsDiamondPullbackModL K M ⊥`, i.e. $\rho(\gamma)$ carries an element with Laurent series $\bar p_{f_1}/\bar p_{g_1}$ to the element with Laurent series $\bar p_f/\bar p_g$ whenever $f_1 = f\mid_k\gamma$ and $g_1 = g\mid_k\gamma$, and for all $\gamma \in \Gamma_0(M)$ and points $P,P'$ of order $M$ with $P' = a \cdot P$ for $a$ the natural number representative of the $(0,0)$ entry of $\gamma$ modulo $M$, one has $\Psi_{P'} = \Psi_P \circ \rho(\gamma)$; (iii) $\Psi_{-P} = \Psi_P$; and (iv) conversely $\Psi_{P'} = \Psi_P$ forces $P' = P$ or $P' = -P$.
--
--   This is the moduli interpretation of the function field of $X_1(M)$ over $K$: a point of exact order $M$ on an elliptic curve with transcendental $j$-invariant determines the evaluation of level-$M$ modular functions at the pair $(E,P)$, the assignment being equivariant for automorphisms of the coefficient field and for the diamond operators, and separating level structures exactly up to sign. Here $\Omega$ is not assumed algebraically closed; full $M$-torsion is imposed directly. It is used by [`ModularCurve.exists_equiv_algHom_qExpFunctionFieldC_gammaH_of_transcendental_j`](thm.html#ModularCurve.exists_equiv_algHom_qExpFunctionFieldC_gammaH_of_transcendental_j) and [`ModularCurve.exists_natural_diamond_algHom_qExpFunctionFieldC_gammaH_of_transcendental_j`](thm.html#ModularCurve.exists_natural_diamond_algHom_qExpFunctionFieldC_gammaH_of_transcendental_j).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_natural_diamond_algHom_qExpFunctionFieldC_gammaH_bot_of_transcendental_j.lean

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_XHDiamondModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve WeierstrassCurve WeierstrassCurve.Affine
open scoped MatrixGroups

universe u v in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_natural_diamond_algHom_qExpFunctionFieldC_gammaH_bot_of_transcendental_j
    (K : Type u) [Field K] [IsAlgClosed K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0)
    (x : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)) (hx : (x : LaurentSeries K) = jqModC K)
    (k Ω : Type v) [Field k] [Field Ω] [DecidableEq Ω] [Algebra K k] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower K k Ω] (E : WeierstrassCurve k) [E.IsElliptic]
    (hE : Transcendental K E.j)
    (hfull : Nat.card {P : (E.baseChange Ω).toAffine.Point // M • P = 0} = M ^ 2) :
    ∃ Ψ : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M} →
        {ψ : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) →ₐ[K] Ω // ψ x = algebraMap k Ω E.j},
      (∀ (σ : Ω ≃ₐ[k] Ω) (P P' : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M}),
        P'.1 = WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P.1 →
          ((Ψ P').1 : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) →ₐ[K] Ω) =
            ((σ : Ω →ₐ[k] Ω).restrictScalars K).comp (Ψ P).1) ∧
      (∀ (ρ : CongruenceSubgroup.Gamma0 M →*
          (qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) ≃ₐ[K]
            qExpFunctionFieldC K (CohCarrier.GammaH M ⊥))),
        IsDiamondPullbackModL K M ⊥ ρ →
        ∀ (γ : CongruenceSubgroup.Gamma0 M)
          (P P' : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M}),
          P'.1 = ((((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M).val) • P.1 →
            ((Ψ P').1 : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) →ₐ[K] Ω) =
              ((Ψ P).1 : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) →ₐ[K] Ω).comp
                (ρ γ : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) →ₐ[K]
                  qExpFunctionFieldC K (CohCarrier.GammaH M ⊥))) ∧
      (∀ P P' : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M},
        P'.1 = -P.1 → Ψ P' = Ψ P) ∧
      (∀ P P' : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M},
        Ψ P' = Ψ P → P'.1 = P.1 ∨ P'.1 = -P.1) := by sorry
