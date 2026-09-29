-- Prove2me | Theorems.Thm_ModularCurve_exists_generator_multiplicativeSubmodule_cornerSubmodule_tateModule_jH_of_ordinary_of_not_isEisenstein_of_mem_infSubgroup
-- name    : ModularCurve.exists_generator_multiplicativeSubmodule_cornerSubmodule_tateModule_jH_of_ordinary_of_not_isEisenstein_of_mem_infSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/40a4e310-7687-5201-aa50-6f7d35f8f8f8
-- title:
--   Rank-one multiplicative submodule at an ordinary non-Eisenstein corner
-- statement:
--   Let $p$ be an odd prime and $M \ge 1$ with $p \mid M$, $p^2 \nmid M$, and let $H \le (\mathbb{Z}/M)^\times$ contain every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$. Let $d \in (\mathbb{Z}/M)^\times$ have image in $\mathbb{Z}/(M/p)$ equal to $p$, and assume that the image of $d$ in $(\mathbb{Z}/(M/p))^\times$, or its negative, lies in [`ModularCurve.infSubgroup`](def/ModularCurve_XHDifferentialsModL.html#L246), the image of $H$ under reduction modulo $M/p$. Let $S$ be a finite set of naturals, and assume `HeckeDiamondInputsHAll M H`: for every prime $\ell$ the inputs `HeckeInputsHAlong` over $\overline{\mathbb{Q}}$ hold at level $(M,H)$ along $\ell$, and every $d \in (\mathbb{Z}/M)^\times$ is realised by a diamond automorphism of the geometric function field of $X_H(M)$. Let $\mathbb{T}$ be a commutative $\mathbb{Z}_p$-algebra acting, compatibly with $\mathbb{Z}_p$, on the Tate module $T =$ [`TateModule p (JH M H)`](def/EllipticCurve_TateModule.html#L15) — sequences $(x_n)$ in the degree-zero divisor class group $J_H(M)(\overline{\mathbb{Q}})$ with $p^n x_n = 0$ and $p\,x_{n+1} = x_n$ — the action being faithful; let $\mathrm{op}$ send each generator in [`CohCarrier.Gen M S`](def/CohCarrier_Inst.html#L13) (the symbols $T_\ell$ for primes $\ell \notin S$, $\ell \nmid M$, $U_q$ for primes $q \mid M$, and $\langle d\rangle$) to an element of $\mathbb{T}$ acting on $T$ as the corresponding operator `tateGenOpH`, and assume the range of $\mathrm{op}$ generates $\mathbb{T}$ as a $\mathbb{Z}_p$-algebra. Let $S'$ be an [`IharaLemma.IdempotentSplitting`](def/IharaLemma_IdempotentSplitting.html#L7) of $\mathbb{T}$ (a complete orthogonal family of idempotents $e_i$ together with maximal ideals $\mathfrak{m}_i$ exhausting the maximal ideals, with $e_i \in \mathfrak{m}_j$ iff $i \neq j$) and $i_0$ an index, $k$ a field of characteristic $p$, $\pi_k$ a ring homomorphism from the corner ring $e_{i_0}\mathbb{T}e_{i_0}$ to $k$, and $\bar\theta$ a function on generators with $\pi_k(e_{i_0}\,\mathrm{op}(g)\,e_{i_0}) = \bar\theta(g)$; assume ordinarity $\bar\theta(U_p) \neq 0$ and non-Eisensteinness: some prime $\ell \notin S$ with $\ell \nmid M$ and $\ell \equiv 1 \bmod M$ has $\bar\theta(T_\ell) \neq \ell + 1$. Let $Pl$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ in its nonunits, and let $P_0$ be a $\mathbb{T}$-submodule of $T$ consisting exactly of those $x$ lying in the corner submodule $e_{i_0} T$ and satisfying $\sigma x = \chi_{\mathrm{cyc},p}(\sigma) \cdot x$ for every $\sigma$ in the inertia subgroup of $Pl$ over $\mathbb{Q}$, where $\chi_{\mathrm{cyc},p}$ is the $p$-adic cyclotomic character. Then there is $x_0 \in P_0$ such that every element of $P_0$ is of the form $a \cdot x_0$ with $a$ in the corner ring, and $a \cdot x_0 = 0$ forces $a = 0$; that is, $P_0$ is free of rank one over $e_{i_0}\mathbb{T}e_{i_0}$ with basis $x_0$.
--
--   This is the statement that the multiplicative (inertially cyclotomic) part of the $p$-adic Tate module of $J_H(M)$, cut out by an ordinary non-Eisenstein corner of the Hecke algebra when $p$ exactly divides $M$ and the class of $p$ lies in $\pm H'$, is free of rank one over that corner ring. It is the input for constructing the ordinary filtration of the associated Galois representation and the resulting parabolic homomorphisms to $\mathrm{GL}_2(\mathbb{Z}_p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_generator_multiplicativeSubmodule_cornerSubmodule_tateModule_jH_of_ordinary_of_not_isEisenstein_of_mem_infSubgroup.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_generator_multiplicativeSubmodule_cornerSubmodule_tateModule_jH_of_ordinary_of_not_isEisenstein_of_mem_infSubgroup
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
    {k : Type} [Field k] [CharP k p] (πk : S'.CornerRing i₀ →+* k) (θbar : CohCarrier.Gen M ↑S → k)
    (hπk : ∀ g : CohCarrier.Gen M ↑S, πk (S'.toCornerRing i₀ (op g)) = θbar g)
    (hord : θbar (CohCarrier.Gen.U p Fact.out hpM) ≠ 0)
    (hEis : ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M), ℓ ≡ 1 [MOD M] ∧
      θbar (CohCarrier.Gen.T ℓ hℓ hℓS hℓM) ≠ (ℓ : k) + 1)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (P0 : Submodule 𝕋 (TateModule p (ModularCurve.JH M H)))
    (hP0 : ∀ x : TateModule p (ModularCurve.JH M H), x ∈ P0 ↔
      x ∈ IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀) ∧
        ∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ModularCurve.JH.tateGaloisRep M H p σ x =
          ((cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) • x) :
    ∃ x₀ ∈ P0,
      (∀ x ∈ P0, ∃ a : S'.CornerRing i₀, x = ((a : S'.CornerRing i₀) : 𝕋) • x₀) ∧
      (∀ a : S'.CornerRing i₀, ((a : S'.CornerRing i₀) : 𝕋) • x₀ = 0 → a = 0) := by sorry
