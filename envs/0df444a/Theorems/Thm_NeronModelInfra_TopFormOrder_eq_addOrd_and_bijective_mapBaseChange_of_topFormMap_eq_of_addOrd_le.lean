-- Prove2me | Theorems.Thm_NeronModelInfra_TopFormOrder_eq_addOrd_and_bijective_mapBaseChange_of_topFormMap_eq_of_addOrd_le
-- name    : NeronModelInfra.TopFormOrder.eq_addOrd_and_bijective_mapBaseChange_of_topFormMap_eq_of_addOrd_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/e5cf2400-069d-5671-a29d-4bdd48dea7ea
-- title:
--   Order squeeze forcing equality and bijective differential base change
-- statement:
--   Fix a discrete valuation ring $R$ (a domain) with a uniformiser $\varpi$ generating its maximal ideal, and fraction field $K$; a discrete valuation ring $R'$ which is a local $R$-algebra with $\mathfrak m_R R' = \mathfrak m_{R'}$ and fraction field $K'$, with $K \to K'$ compatible over $R$. On one side, let $O_0$ be a discrete valuation ring, a local $R$-algebra with $\mathfrak m_R O_0 = \mathfrak m_{O_0}$, with fraction field $F_0 \supseteq K$, let $d$ be a natural number, $b_0$ a basis of $\Omega_{O_0/R}$ indexed by $\mathrm{Fin}\,d$, and $a \in F_0$ nonzero. On the other side, let $O_1$ be a commutative $R$-algebra with a basis $b_1$ of $\Omega_{O_1/R}$ indexed by $\mathrm{Fin}\,d$, a unit $w_1 \in O_1^\times$ and an integer $m$, and let $O'$ be a domain which is an $R'$- and $O_1$-algebra compatibly over $R$, such that the composite of `KaehlerDifferential.mapBaseChange R O₁ O'` with (the restriction of scalars to $O'$ of) `KaehlerDifferential.map R R' O' O'` is bijective, i.e. $O' \otimes_{O_1} \Omega_{O_1/R} \to \Omega_{O'/R'}$ is bijective. Let $O$ be a discrete valuation ring, a local $R'$-algebra with $\mathfrak m_{R'} O = \mathfrak m_O$, receiving compatible maps from $O_0$ (local), from $O_1$ and from $O'$, with $O \otimes_{O_0} \Omega_{O_0/R} \to \Omega_{O/R'}$ (the analogous composite for `KaehlerDifferential.mapBaseChange R O₀ O`) bijective, and let $F$ be a field which is simultaneously a fraction field of $O$ and of $O'$, containing $K'$ and $F_0$ compatibly over the base rings. Let $\sigma \in \bigwedge^d_F \Omega_{F/K}$ satisfy: $\sigma = \bigl(w_1 \varpi^{m}\bigr)_F \cdot \mathrm{topFormMap}(b_1)$, where $\mathrm{topFormMap}$ denotes the induced map $\bigwedge^d_{O_1} \Omega_{O_1/R} \to \bigwedge^d_F \Omega_{F/K}$ applied to $b_1^{\wedge}$ and the scalar is $\mathrm{algebraMap}(w_1)$ times the integer power $\mathrm{algebraMap}(\varpi)^m$ in $F$; and, after restricting the base field from $K$ to $K'$, $\sigma$ has the same image in $\bigwedge^d_F \Omega_{F/K'}$ as the pushforward of $a \cdot b_0^{\wedge}$ from $\bigwedge^d_{F_0} \Omega_{F_0/K}$. Assume moreover $\mathrm{addOrd}_{O_0}(a) \le m$, where $\mathrm{addOrd}$ is the additive valuation of $F_0$ at the maximal ideal of $O_0$ (set to $0$ at $0$). Then $m = \mathrm{addOrd}_{O_0}(a)$, and `KaehlerDifferential.mapBaseChange R' O' O`, that is $O \otimes_{O'} \Omega_{O'/R'} \to \Omega_{O/R'}$, is bijective.
--
--   This is the local algebra underlying the statement that, for a minimal form, the order of vanishing computed on a translated model agrees with the order computed on the original one, and that equality forces smoothness-type base change of differentials (Bosch–Lütkebohmert–Raynaud 4.3, Proposition 4(iii)). It is used by [`NeronModelInfra.exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul`](thm.html#NeronModelInfra.exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul), where $R'$, $O$, $O_0$, $O_1$, $O'$ are local rings of the relevant schemes at the points in play and $\sigma$ is the value of the top form at the corresponding $F$-point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_TopFormOrder_eq_addOrd_and_bijective_mapBaseChange_of_topFormMap_eq_of_addOrd_le.lean

import Mathlib
import Definitions.Def_NeronModelInfra_TopFormOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct NeronModelInfra.TopFormOrder

theorem NeronModelInfra.TopFormOrder.eq_addOrd_and_bijective_mapBaseChange_of_topFormMap_eq_of_addOrd_le

    (R K R' K' : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')]
    (hRR' : Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R')
    [Field K'] [Algebra R' K'] [IsFractionRing R' K'] [Algebra K K'] [Algebra R K']
    [IsScalarTower R K K'] [IsScalarTower R R' K']

    (O₀ F₀ : Type u)
    [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀] [Algebra R O₀] [IsLocalHom (algebraMap R O₀)]
    (hO₀ : Ideal.map (algebraMap R O₀) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal O₀)
    [Field F₀] [Algebra O₀ F₀] [IsFractionRing O₀ F₀] [Algebra K F₀] [Algebra R F₀]
    [IsScalarTower R O₀ F₀] [IsScalarTower R K F₀]
    (d : ℕ) (b₀ : Module.Basis (Fin d) O₀ (Ω[O₀⁄R])) (a : F₀) (ha : a ≠ 0)

    (O₁ O' : Type u)
    [CommRing O₁] [Algebra R O₁]
    [CommRing O'] [IsDomain O'] [Algebra R' O'] [Algebra O₁ O'] [Algebra R O']
    [IsScalarTower R O₁ O'] [IsScalarTower R R' O']
    (b₁ : Module.Basis (Fin d) O₁ (Ω[O₁⁄R])) (w₁ : O₁ˣ) (m : ℤ)
    (hbc' : Function.Bijective
      ((KaehlerDifferential.map R R' O' O').restrictScalars O' ∘ₗ KaehlerDifferential.mapBaseChange R O₁ O'))

    (O F : Type u)
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra R' O] [IsLocalHom (algebraMap R' O)]
    (hO : Ideal.map (algebraMap R' O) (IsLocalRing.maximalIdeal R') = IsLocalRing.maximalIdeal O)
    [Algebra R O] [IsScalarTower R R' O]
    [Algebra O₀ O] [IsLocalHom (algebraMap O₀ O)] [IsScalarTower R O₀ O]
    [Algebra O' O] [IsScalarTower R' O' O] [Algebra O₁ O] [IsScalarTower O₁ O' O] [IsScalarTower R O₁ O]
    (hbc : Function.Bijective
      ((KaehlerDifferential.map R R' O O).restrictScalars O ∘ₗ KaehlerDifferential.mapBaseChange R O₀ O))
    [Field F] [Algebra O F] [IsFractionRing O F] [Algebra O' F] [IsScalarTower O' O F] [IsFractionRing O' F]
    [Algebra K' F] [Algebra R' F] [IsScalarTower R' O F] [IsScalarTower R' O' F] [IsScalarTower R' K' F]
    [Algebra K F] [Algebra R F] [IsScalarTower R O F] [IsScalarTower R K F] [IsScalarTower K K' F]
    [Algebra F₀ F] [Algebra O₀ F] [IsScalarTower O₀ O F] [IsScalarTower O₀ F₀ F] [IsScalarTower K F₀ F]
    [Algebra O₁ F] [IsScalarTower O₁ O F] [IsScalarTower R O₁ F]

    (σ : ⋀[F]^d (Ω[F⁄K]))
    (hT : σ = (algebraMap O₁ F (w₁ : O₁) * algebraMap O₁ F (algebraMap R O₁ ϖ) ^ m) •
        topFormMap R K O₁ F d (exteriorPower.ιMulti O₁ d b₁))
    (hX : topFormMap K K' F F d σ =
        topFormMap K K' F₀ F d (a • topFormMap R K O₀ F₀ d (exteriorPower.ιMulti O₀ d b₀)))
    (hmin : addOrd O₀ F₀ a ≤ m) :
    m = addOrd O₀ F₀ a ∧ Function.Bijective (KaehlerDifferential.mapBaseChange R' O' O) := by sorry
