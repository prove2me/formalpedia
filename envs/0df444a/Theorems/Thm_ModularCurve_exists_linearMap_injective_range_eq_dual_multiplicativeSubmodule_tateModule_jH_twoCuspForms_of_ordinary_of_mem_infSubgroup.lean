-- Prove2me | Theorems.Thm_ModularCurve_exists_linearMap_injective_range_eq_dual_multiplicativeSubmodule_tateModule_jH_twoCuspForms_of_ordinary_of_mem_infSubgroup
-- name    : ModularCurve.exists_linearMap_injective_range_eq_dual_multiplicativeSubmodule_tateModule_jH_twoCuspForms_of_ordinary_of_mem_infSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/1072d3f8-2c41-51fe-8945-cb0cc6cd1023
-- title:
--   Mod-p two-cusp forms dual to the multiplicative part
-- statement:
--   Let $p$ be an odd prime, $M\ge 1$ with $p\mid M$ and $p^2\nmid M$, and let $H\le(\mathbb Z/M)^\times$ contain every unit whose reduction in $(\mathbb Z/(M/p))^\times$ is $1$. Let $d\in(\mathbb Z/M)^\times$ reduce to $p$ in $\mathbb Z/(M/p)$, and assume the reduction of $d$ or of $-d$ lies in [`ModularCurve.infSubgroup p M H hpM`](def/ModularCurve_XHDifferentialsModL.html#L246), the image of $H$ in $(\mathbb Z/(M/p))^\times$. Fix a set $S$ of naturals and assume the project's hypothesis [`ModularCurve.HeckeDiamondInputsHAll M H`](def/ModularCurve_XHOperators.html#L113) (Hecke inputs along every prime, and a diamond automorphism of the geometric function field for each $d$). Let $\mathbb T$ be a commutative $\mathbb Z_p$-algebra acting on the Tate module $T_pJ_H(M)=\{x:\mathbb N\to J_H(M)\mid p^nx_n=0,\ px_{n+1}=x_n\}$, where $J_H(M)=\mathrm{Pic}^0$ of the geometric function field of $X_H(M)$, compatibly with $\mathbb Z_p$ and faithfully, and let $\mathrm{op}:\mathrm{Gen}(M,S)\to\mathbb T$ send each generator $T_\ell$, $U_q$, $\langle d\rangle$ to an element acting as the corresponding covariant operator [`ModularCurve.tateGenOpH`](def/ModularCurve_XHOperators.html#L99), with $\mathbb Z_p[\mathrm{range}\,\mathrm{op}]=\mathbb T$. Let $S'$ be an idempotent splitting of $\mathbb T$ (complete orthogonal idempotents $e_i$ matched with all maximal ideals $\mathfrak m_i$, $e_i\in\mathfrak m_j\iff i\ne j$), $i_0$ an index with $\mathrm{op}(U_p)\notin\mathfrak m_{i_0}$, and $Pl$ a valuation subring of $\overline{\mathbb Q}$ with $p$ a nonunit. Let $P_0$ be the $\mathbb T$-submodule consisting of the $x$ in the image of $e_{i_0}$ on which the inertia subgroup of $Pl$ over $\mathbb Q$ acts through the $p$-adic cyclotomic character. Finally let $A\subseteq\mathbb C$ be a subring, $I\subseteq A$ an ideal with $p\in I$, and $\tau:\mathbb T\to\mathrm{End}_{A/I}(\mathcal C)$ a ring homomorphism sending $\mathrm{op}(g)$ to [`CuspForm.twoCuspGenMod I S g`](def/CuspForm_TwoCuspLattice.html#L200), where $\mathcal C$ is the reduction modulo $I$ of the $A$-lattice of two-cusp integral weight-$2$ cusp forms on $\Gamma_H(M)$. Then there is an injective $A/I$-linear map $\Theta$ from the additive homomorphisms $P_0\to A/I$ into $\mathcal C$ such that $\Theta(\varphi\circ t)=\tau(t)(\Theta\varphi)$ for all $t\in\mathbb T$, and the range of $\Theta$ equals the range of $\tau(e_{i_0})$.
--
--   This is the ordinary-component case of Wiles' duality between the local factor of the mod-$p$ two-cusp forms of weight $2$ on $X_H(M)$ and the $\mathbb Z_p$-dual of the cyclotomic-inertia part $P^0$ of the $e_{i_0}$-component of $T_pJ_H(M)$, under $p\|M$ with $\bar p\in\pm H'$. It is obtained by transporting the corresponding characteristic-$p$ statement about polar differentials on the good component of the special fibre of $X_{H'}(M/p)$, and is used in turn to identify semilinear maps on $P^0$ with the two-cusp eigenspace.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_linearMap_injective_range_eq_dual_multiplicativeSubmodule_tateModule_jH_twoCuspForms_of_ordinary_of_mem_infSubgroup.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_CuspForm_TwoCuspLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_linearMap_injective_range_eq_dual_multiplicativeSubmodule_tateModule_jH_twoCuspForms_of_ordinary_of_mem_infSubgroup
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (d : (ZMod M)ˣ) (hd : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (hdH : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ ModularCurve.infSubgroup p M H hpM ∨
      -ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ ModularCurve.infSubgroup p M H hpM)
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
    (A : Subring ℂ) (I : Ideal A) (hpI : (p : A) ∈ I)
    (τ : 𝕋 →+* Module.End (A ⧸ I) (CuspForm.TwoCuspForms M H 2 p A I))
    (hτ : ∀ g : CohCarrier.Gen M S, τ (op g) = CuspForm.twoCuspGenMod I S g) :
    ∃ Θ : (↥P0 →+ A ⧸ I) →ₗ[A ⧸ I] CuspForm.TwoCuspForms M H 2 p A I,
      Function.Injective Θ ∧
      (∀ (t : 𝕋) (φ ψ : ↥P0 →+ A ⧸ I), (∀ x : ↥P0, ψ x = φ (t • x)) → Θ ψ = τ t (Θ φ)) ∧
      LinearMap.range Θ = LinearMap.range (τ (S'.e i₀)) := by sorry
