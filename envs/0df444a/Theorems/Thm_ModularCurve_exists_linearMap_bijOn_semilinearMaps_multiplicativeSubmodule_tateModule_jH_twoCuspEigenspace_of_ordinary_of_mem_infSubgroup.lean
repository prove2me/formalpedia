-- Prove2me | Theorems.Thm_ModularCurve_exists_linearMap_bijOn_semilinearMaps_multiplicativeSubmodule_tateModule_jH_twoCuspEigenspace_of_ordinary_of_mem_infSubgroup
-- name    : ModularCurve.exists_linearMap_bijOn_semilinearMaps_multiplicativeSubmodule_tateModule_jH_twoCuspEigenspace_of_ordinary_of_mem_infSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/ffa69522-5217-5ae8-a4c1-65d64bfc1d35
-- title:
--   Ordinary multiplicative submodule dual to mod-p two-cusp eigenspace
-- statement:
--   Let $p$ be an odd prime, let $M\ge 1$ satisfy $p\mid M$ and $p^2\nmid M$, and let $H\le(\mathbb{Z}/M)^\times$ contain every unit mapping to $1$ in $(\mathbb{Z}/(M/p))^\times$. Let $d\in(\mathbb{Z}/M)^\times$ have image $p$ in $\mathbb{Z}/(M/p)$, and assume that this image, or its negative, lies in [`ModularCurve.infSubgroup`](def/ModularCurve_XHDifferentialsModL.html#L246), the image of $H$ in $(\mathbb{Z}/(M/p))^\times$. Let $S$ be a finite set of naturals and assume [`ModularCurve.HeckeDiamondInputsHAll M H`](def/ModularCurve_XHOperators.html#L113): the Hecke inputs at every prime for $X_H(M)$ over $\overline{\mathbb{Q}}$, together with, for each $d$, an automorphism of the function field realising the diamond operator. Let $\mathbb{T}$ be a commutative $\mathbb{Z}_p$-algebra acting faithfully on the Tate module $T_pJ_H=\{(x_n)\in(J_H)^{\mathbb{N}}: p^nx_n=0,\ px_{n+1}=x_n\}$ of $J_H=\mathrm{Pic}^0$ of $X_H(M)$ over $\overline{\mathbb{Q}}$, compatibly with the $\mathbb{Z}_p$-structure, and let $\mathrm{op}$ send each generator $g$ (a $T_\ell$ with $\ell$ prime, $\ell\notin S$, $\ell\nmid M$; a $U_q$ with $q\mid M$ prime; or a diamond $\langle d\rangle$) to an element of $\mathbb{T}$ acting as [`ModularCurve.tateGenOpH`](def/ModularCurve_XHOperators.html#L99), with $\mathbb{T}$ generated over $\mathbb{Z}_p$ by the range of $\mathrm{op}$. Let $S'$ be an idempotent splitting of $\mathbb{T}$ (complete orthogonal idempotents $e_i$ matched with all maximal ideals $\mathfrak{m}_i$, $e_i\in\mathfrak{m}_j$ iff $i\ne j$), fix $i_0$ with $\mathrm{op}(U_p)\notin\mathfrak{m}_{i_0}$, let $Pl$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit, and let $P_0$ be the $\mathbb{T}$-submodule of those $x$ in the corner submodule $e_{i_0}\cdot T_pJ_H$ with $\sigma x=\chi_{\mathrm{cyc},p}(\sigma)x$ for all $\sigma$ in the inertia subgroup attached to $Pl$ over $\mathbb{Q}$. Then there exist a subring $A\subseteq\mathbb{C}$ and $\pi\in A$ with $(\pi)$ maximal and $p\in(\pi)$, a ring homomorphism $j:\mathbb{T}\to A/(\pi)$ vanishing on $\mathfrak{m}_{i_0}$, and an $A/(\pi)$-linear map $\Psi$ from the additive maps $P_0\to A/(\pi)$ to the two-cusp forms $\mathrm{TwoCuspForms}(M,H,2,p,A,(\pi))$, such that every $j$-semilinear $\varphi$ (i.e. $\varphi(tx)=j(t)\varphi(x)$) has $\Psi\varphi$ in the eigenspace where each $\mathrm{twoCuspGenMod}(g)$ acts by $j(\mathrm{op}(g))$, with $\Psi\varphi=0$ only for $\varphi=0$, and every element of that eigenspace is $\Psi\varphi$ for some $j$-semilinear $\varphi$; thus $\Psi$ is a bijection from the $j$-semilinear maps onto the eigenspace.
--
--   This is the duality identifying the $A/(\pi)$-dual of the inertia-multiplicative part of the ordinary component of $T_pJ_H(M)$ with the corresponding eigenspace of mod-$p$ two-cusp forms, in the form used by Wiles at a level exactly divisible by $p$ with the class of $p$ in $\pm H'$. It is the second of the two duality statements of this shape and is cited in the derivation that the Hecke action on the multiplicative submodule is congruent to a scalar modulo the maximal ideal away from the Eisenstein case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_linearMap_bijOn_semilinearMaps_multiplicativeSubmodule_tateModule_jH_twoCuspEigenspace_of_ordinary_of_mem_infSubgroup.lean

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

theorem ModularCurve.exists_linearMap_bijOn_semilinearMaps_multiplicativeSubmodule_tateModule_jH_twoCuspEigenspace_of_ordinary_of_mem_infSubgroup
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (d : (ZMod M)ˣ) (hd : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (hdH : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ ModularCurve.infSubgroup p M H hpM ∨
      -ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ ModularCurve.infSubgroup p M H hpM)
    (S : Finset ℕ) (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 (TateModule p (ModularCurve.JH M H))]
    [IsScalarTower ℤ_[p] 𝕋 (TateModule p (ModularCurve.JH M H))]
    (hfaith : ∀ t : 𝕋, (∀ x : TateModule p (ModularCurve.JH M H), t • x = 0) → t = 0)
    (op : CohCarrier.Gen M ↑S → 𝕋)
    (hop : ∀ (g : CohCarrier.Gen M ↑S) (x : TateModule p (ModularCurve.JH M H)),
      op g • x = ModularCurve.tateGenOpH M H ↑S p g x)
    (hgen : Algebra.adjoin ℤ_[p] (Set.range op) = ⊤)
    (S' : IharaLemma.IdempotentSplitting 𝕋) (i₀ : Fin S'.n)
    (hord : op (CohCarrier.Gen.U p Fact.out hpM) ∉ S'.𝔪 i₀)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (P0 : Submodule 𝕋 (TateModule p (ModularCurve.JH M H)))
    (hP0 : ∀ x : TateModule p (ModularCurve.JH M H), x ∈ P0 ↔
      x ∈ IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀) ∧
        ∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ModularCurve.JH.tateGaloisRep M H p σ x =
          ((cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) • x) :
    ∃ (A : Subring ℂ) (π : A) (_ : (Ideal.span ({π} : Set A)).IsMaximal)
      (_ : (p : A) ∈ Ideal.span ({π} : Set A))
      (j : 𝕋 →+* A ⧸ Ideal.span ({π} : Set A)) (_ : ∀ t ∈ S'.𝔪 i₀, j t = 0)
      (Ψ : (↥P0 →+ A ⧸ Ideal.span ({π} : Set A)) →ₗ[A ⧸ Ideal.span ({π} : Set A)]
        CuspForm.TwoCuspForms M H 2 p A (Ideal.span ({π} : Set A))),
      (∀ φ : ↥P0 →+ A ⧸ Ideal.span ({π} : Set A),
        (∀ (t : 𝕋) (x : ↥P0), φ (t • x) = j t * φ x) →
          Ψ φ ∈ CuspForm.twoCuspEigenspace (Ideal.span ({π} : Set A)) ↑S (fun g => j (op g)) ∧
          (Ψ φ = 0 → φ = 0)) ∧
      (∀ ω ∈ CuspForm.twoCuspEigenspace (Ideal.span ({π} : Set A)) ↑S (fun g => j (op g)),
        ∃ φ : ↥P0 →+ A ⧸ Ideal.span ({π} : Set A),
          (∀ (t : 𝕋) (x : ↥P0), φ (t • x) = j t * φ x) ∧ Ψ φ = ω) := by sorry
