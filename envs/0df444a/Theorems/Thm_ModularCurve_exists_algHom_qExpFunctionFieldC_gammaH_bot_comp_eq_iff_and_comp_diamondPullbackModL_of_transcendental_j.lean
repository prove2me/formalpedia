-- Prove2me | Theorems.Thm_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_bot_comp_eq_iff_and_comp_diamondPullbackModL_of_transcendental_j
-- name    : ModularCurve.exists_algHom_qExpFunctionFieldC_gammaH_bot_comp_eq_iff_and_comp_diamondPullbackModL_of_transcendental_j
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/8b0ff406-c1c6-5055-bc4c-85c9b8e5f03e
-- title:
--   Generic evaluation of the Γ₁(M) function field with torsion point
-- statement:
--   Let $K$ be an algebraically closed field, $M$ a non-zero natural number with $M \neq 0$ in $K$, and write $F =$ `qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)` for the intermediate field of $K((q))$ generated over $K$ by all quotients $\bar p_f/\bar p_g$, where $f,g$ are modular forms of one and the same weight on the subgroup of $\mathrm{SL}_2(\mathbb Z)$ consisting of the matrices of $\Gamma_0(M)$ whose image under `gamma0Units M` is trivial, $p_f,p_g \in \mathbb Z[[q]]$ are integral power series whose complex images are the $q$-expansions of $f$ and $g$, and $\bar p_g \neq 0$ after coefficientwise reduction into $K$. Let $x \in F$ be an element whose Laurent series is `jqModC K`, the series $q^{-1}\bar p$ attached to `jNum` $= E_4^3 \cdot$ `dedekindEtaUnitInv`. Let $k$ and $\Omega$ be fields that are $K$-algebras with $\Omega$ a $k$-algebra compatibly, $\Omega$ an algebraic closure of $k$, and let $E$ be an elliptic Weierstrass curve over $k$ whose $j$-invariant is transcendental over $K$ and generates $k$ over $K$, i.e. $K(E.j) = k$. Then there are a point $P_0$ on the affine model of $E$ base changed to $\Omega$ and a $K$-algebra homomorphism $\psi_0 \colon F \to \Omega$ such that: $P_0$ has additive order exactly $M$; $\psi_0(x)$ is the image of $E.j$ in $\Omega$; for every $\sigma \in \mathrm{Aut}_k(\Omega)$ one has $\sigma(P_0) = P_0$ or $\sigma(P_0) = -P_0$ if and only if $\sigma \circ \psi_0 = \psi_0$; and for every group homomorphism $\rho$ from $\Gamma_0(M)$ to the $K$-algebra automorphisms of $F$ satisfying `IsDiamondPullbackModL K M ⊥ ρ` — that is, whenever $f_1 = f|_k\gamma$ and $g_1 = g|_k\gamma$ for forms of weight $k$ on that subgroup with integral $q$-expansions $p_f,p_g,p_{f_1},p_{g_1}$, $\bar p_g \neq 0$, and $y \in F$ has Laurent series $\bar p_{f_1}/\bar p_{g_1}$, then $\rho(\gamma)(y)$ has Laurent series $\bar p_f/\bar p_g$ — and for every $\gamma \in \Gamma_0(M)$, there is $\sigma \in \mathrm{Aut}_k(\Omega)$ with $\sigma(P_0) = a \cdot P_0$, where $a$ is the natural-number representative of the upper-left entry $\gamma_{00}$ of $\gamma$ modulo $M$, and $\psi_0 \circ \rho(\gamma) = \sigma \circ \psi_0$.
--
--   This is the arithmetic (Kroneckerian) description of the function field of the modular curve of level $\Gamma_1(M)$ as the field of modular functions evaluated at a generic pair (elliptic curve, point of exact order $M$): the embedding $\psi_0$ realises the field inside an algebraic closure of $K(j)$, its stabiliser in $\mathrm{Aut}_k(\Omega)$ is exactly the stabiliser of $P_0$ up to sign, and the diamond operators act through $P_0 \mapsto a P_0$. It feeds the construction of the natural diamond action in [`ModularCurve.exists_natural_diamond_algHom_qExpFunctionFieldC_gammaH_bot_of_transcendental_j`](thm.html#ModularCurve.exists_natural_diamond_algHom_qExpFunctionFieldC_gammaH_bot_of_transcendental_j).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_bot_comp_eq_iff_and_comp_diamondPullbackModL_of_transcendental_j.lean

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_XHDiamondModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve WeierstrassCurve WeierstrassCurve.Affine
open scoped MatrixGroups

universe u v in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_algHom_qExpFunctionFieldC_gammaH_bot_comp_eq_iff_and_comp_diamondPullbackModL_of_transcendental_j
    (K : Type u) [Field K] [IsAlgClosed K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0)
    (x : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)) (hx : (x : LaurentSeries K) = jqModC K)
    (k Ω : Type v) [Field k] [Field Ω] [DecidableEq Ω] [Algebra K k] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower K k Ω] [IsAlgClosure k Ω] (E : WeierstrassCurve k) [E.IsElliptic]
    (hE : Transcendental K E.j) (hgen : IntermediateField.adjoin K ({E.j} : Set k) = ⊤) :
    ∃ (P₀ : (E.baseChange Ω).toAffine.Point)
      (ψ₀ : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) →ₐ[K] Ω),
      addOrderOf P₀ = M ∧ ψ₀ x = algebraMap k Ω E.j ∧
      (∀ σ : Ω ≃ₐ[k] Ω,
        (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P₀ = P₀ ∨
            WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P₀ = -P₀) ↔
          ((σ : Ω →ₐ[k] Ω).restrictScalars K).comp ψ₀ = ψ₀) ∧
      (∀ (ρ : CongruenceSubgroup.Gamma0 M →*
          (qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) ≃ₐ[K]
            qExpFunctionFieldC K (CohCarrier.GammaH M ⊥))),
        IsDiamondPullbackModL K M ⊥ ρ →
        ∀ γ : CongruenceSubgroup.Gamma0 M, ∃ σ : Ω ≃ₐ[k] Ω,
          WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P₀ =
              ((((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M).val) • P₀ ∧
            ψ₀.comp (ρ γ : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) →ₐ[K]
                qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)) =
              ((σ : Ω →ₐ[k] Ω).restrictScalars K).comp ψ₀) := by sorry
