-- Prove2me | Theorems.Thm_ModularCurve_exists_linearMap_injective_range_eq_dual_multiplicativeSubmodule_tateModule_jH_ssPolarDifferentials_of_ordinary_of_mem_infSubgroup
-- name    : ModularCurve.exists_linearMap_injective_range_eq_dual_multiplicativeSubmodule_tateModule_jH_ssPolarDifferentials_of_ordinary_of_mem_infSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/785d0be0-95f8-5086-a689-c918f247f4c2
-- title:
--   Ordinary duality: multiplicative part of TₚJ_H and polar differentials
-- statement:
--   Let $p$ be an odd prime, $M\neq 0$ with $p\mid M$ and $p^2\nmid M$, and let $H\le(\mathbb{Z}/M)^\times$ contain every unit reducing to $1$ in $(\mathbb{Z}/(M/p))^\times$; let $S\subseteq\mathbb{N}$ and assume [`ModularCurve.HeckeDiamondInputsHAll M H`](def/ModularCurve_XHOperators.html#L113), i.e. the Hecke inputs at every prime $\ell$ for $X_H(M)$ over $\overline{\mathbb{Q}}$ together with, for each $d\in(\mathbb{Z}/M)^\times$, a diamond automorphism of `xHFunctionFieldBar M H`. Let $\mathbb{T}$ be a commutative $\mathbb{Z}_p$-algebra acting on $T_p(J_H)=$ [`TateModule p (ModularCurve.JH M H)`](def/EllipticCurve_TateModule.html#L15) compatibly with $\mathbb{Z}_p$ and faithfully, and let `op` assign to each formal generator $T_\ell$, $U_q$, $\langle d\rangle$ an element of $\mathbb{T}$ acting as [`ModularCurve.tateGenOpH`](def/ModularCurve_XHOperators.html#L99), the range of `op` generating $\mathbb{T}$ over $\mathbb{Z}_p$. Let $S'$ be an idempotent splitting of $\mathbb{T}$ (complete orthogonal idempotents $e_i$ matched with all maximal ideals $\mathfrak{m}_i$ via $e_i\in\mathfrak{m}_j\iff i\neq j$) and $i_0$ an index with $\mathrm{op}(U_p)\notin\mathfrak{m}_{i_0}$ (ordinarity). Let $Pl$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ in its nonunits, and let $P_0$ be a $\mathbb{T}$-submodule consisting exactly of those $x$ in the image of $e_{i_0}$ on $T_p(J_H)$ with $\sigma x=\chi_{\mathrm{cyc}}(\sigma)x$ for all $\sigma$ in the inertia subgroup of $Pl$ over $\mathbb{Q}$. Let $K$ be an algebraically closed field with a $\mathbb{Z}/p$-algebra structure and $\tau$ a ring homomorphism from $\mathbb{T}$ to the $K$-endomorphisms of [`ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M/p) (ModularCurve.infSubgroup p M H hpM)) p`](def/ModularCurve_XHDifferentialsModL.html#L35) (differentials of the $q$-expansion function field of $\Gamma_{H'}(M/p)$ with poles only at the supersingular places), such that $\tau(\mathrm{op}(g))$ acts by [`ModularCurve.genDiffModL`](def/ModularCurve_XHDifferentialsModL.html#L266) on underlying differentials for every generator $g$. Finally let $d\in(\mathbb{Z}/M)^\times$ have image $p$ in $\mathbb{Z}/(M/p)$, with that image or its negative lying in the image $H'$ of $H$. Then there is an injective $K$-linear map $\Psi$ from the additive homomorphisms $P_0\to K$ into these supersingular-polar differentials such that $\Psi(\varphi\circ t)=\tau(t)(\Psi\varphi)$ for all $t\in\mathbb{T}$ (stated via $\psi x=\varphi(t\cdot x)$) and such that the range of $\Psi$ equals the range of $\tau(e_{i_0})$.
--
--   This is the geometric comparison at an ordinary maximal ideal from Wiles' Chapter 2 §1, (2.5)–(2.9): the multiplicative part $P^0$ of the $p$-adic Tate module of $J_H(M)$ cut out by the idempotent $e_{i_0}$ has $K$-dual Hecke-equivariantly identified with the $e_{i_0}$-part of the differentials on $X_{H'}(M/p)$ over $K$ with poles only at the supersingular points. It is used to derive the corresponding duality statement phrased in terms of two-cusp mod $p$ cusp forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_linearMap_injective_range_eq_dual_multiplicativeSubmodule_tateModule_jH_ssPolarDifferentials_of_ordinary_of_mem_infSubgroup.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_linearMap_injective_range_eq_dual_multiplicativeSubmodule_tateModule_jH_ssPolarDifferentials_of_ordinary_of_mem_infSubgroup
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (S : Set ℕ) (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 (TateModule p (ModularCurve.JH M H))]
    [IsScalarTower ℤ_[p] 𝕋 (TateModule p (ModularCurve.JH M H))]
    (hfaith : ∀ t : 𝕋, (∀ x : TateModule p (ModularCurve.JH M H), t • x = 0) → t = 0)
    (op : CohCarrier.Gen M S → 𝕋)
    (hop : ∀ (g : CohCarrier.Gen M S) (x : TateModule p (ModularCurve.JH M H)),
      op g • x = ModularCurve.tateGenOpH M H S p g x)
    (hgen : Algebra.adjoin ℤ_[p] (Set.range op) = ⊤)
    (S' : IharaLemma.IdempotentSplitting 𝕋) (i₀ : Fin S'.n)
    (hord : op (CohCarrier.Gen.U p Fact.out hpM) ∉ S'.𝔪 i₀)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (P0 : Submodule 𝕋 (TateModule p (ModularCurve.JH M H)))
    (hP0 : ∀ x : TateModule p (ModularCurve.JH M H), x ∈ P0 ↔
      x ∈ IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀) ∧
        ∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ModularCurve.JH.tateGaloisRep M H p σ x =
          ((cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) • x)
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra (ZMod p) K]
    (τ : 𝕋 →+* Module.End K
      (ModularCurve.ssPolarDifferentials K
        (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p))
    (hτ : ∀ (g : CohCarrier.Gen M S)
      (ω : ModularCurve.ssPolarDifferentials K
        (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p),
      ((τ (op g) ω : ModularCurve.ssPolarDifferentials K
          (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) :
        Ω[ModularCurve.qExpFunctionFieldC K
            (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
        ModularCurve.genDiffModL K p M H hpM S g ω)

    (d : (ZMod M)ˣ) (hd : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (hdH : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ ModularCurve.infSubgroup p M H hpM ∨
      -ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ ModularCurve.infSubgroup p M H hpM)
    :
    ∃ Ψ : (↥P0 →+ K) →ₗ[K]
        ModularCurve.ssPolarDifferentials K
          (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p,
      Function.Injective Ψ ∧
      (∀ (t : 𝕋) (φ ψ : ↥P0 →+ K), (∀ x : ↥P0, ψ x = φ (t • x)) → Ψ ψ = τ t (Ψ φ)) ∧
      LinearMap.range Ψ = LinearMap.range (τ (S'.e i₀)) := by sorry
