-- Prove2me | Theorems.Thm_ModularCurve_exists_adaptedLatticeBasis_inertiaEigenspace_cornerSubmodule_tateModule_jH_of_ordinary
-- name    : ModularCurve.exists_adaptedLatticeBasis_inertiaEigenspace_cornerSubmodule_tateModule_jH_of_ordinary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/1af40510-f4a8-5cc3-8e17-0eed11928c8d
-- title:
--   Adapted basis of the p-ordinary corner of Tₚ J_H
-- statement:
--   Let $p$ be a prime with $p \neq 2$, let $M \geq 1$ satisfy $p \mid M$ and $p^2 \nmid M$, and let $H \leq (\mathbb{Z}/M)^\times$ contain every unit whose image under reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is $1$; let $S$ be a finite set of naturals and assume [`ModularCurve.HeckeDiamondInputsHAll M H`](def/ModularCurve_XHOperators.html#L113), i.e. for every prime $\ell$ the Hecke inputs `HeckeInputsHAlong` hold for $M,H,\ell$ over $\overline{\mathbb{Q}}$, and every $d \in (\mathbb{Z}/M)^\times$ is realised by a diamond automorphism of the base-changed function field of $X_H$. Write $T =$ [`TateModule p (JH M H)`](def/EllipticCurve_TateModule.html#L15), the group of sequences $(x_n)$ in the degree-zero divisor class group $\mathrm{Pic}^0$ of that function field with $p^n x_n = 0$ and $p\,x_{n+1} = x_n$, and $\rho =$ `JH.tateGaloisRep` for its $\mathbb{Z}_p$-linear $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$-action. Let $\mathbb{T}$ be a commutative $\mathbb{Z}_p$-algebra acting on $T$ compatibly with the $\mathbb{Z}_p$-structure and faithfully (only $0$ annihilates all of $T$), and let $op :$ [`CohCarrier.Gen M S`](def/CohCarrier_Inst.html#L13) $\to \mathbb{T}$, on the generators $T_\ell$ ($\ell$ prime, $\ell \notin S$, $\ell \nmid M$), $U_q$ ($q$ prime, $q \mid M$) and $\langle d \rangle$, act on $T$ as the corresponding operators `tateGenOpH`, with $\mathbb{Z}_p$-adjoin of the range of $op$ equal to $\mathbb{T}$. Let $S'$ be an idempotent splitting of $\mathbb{T}$ (complete orthogonal idempotents $e_i$ together with maximal ideals $\mathfrak{m}_i$ exhausting the maximal ideals and satisfying $e_i \in \mathfrak{m}_j \iff i \neq j$) and $i_0$ an index; put $A =$ `S'.CornerRing i₀`, the corner ring of $e = e_{i_0}$, and $P =$ `cornerSubmodule (S'.e i₀)` $= e \cdot T$. Assume a ring homomorphism $\pi_k : A \to k$ into a field $k$ of characteristic $p$ and $\bar\theta$ on the generators with $\pi_k(e\,op(g)\,e) = \bar\theta(g)$ for all $g$, and the ordinarity condition $\bar\theta(U_p) \neq 0$. Let $Pl$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of it, with inertia subgroup over $\mathbb{Q}$ as in `inertiaSubgroupIn`, and let $P^0 \subseteq T$ be a $\mathbb{T}$-submodule whose elements are exactly the $x \in P$ with $\rho(\sigma)x = \varepsilon(\sigma)x$ for all $\sigma$ in that inertia subgroup, $\varepsilon$ the $p$-adic cyclotomic character viewed in $\mathbb{Z}_p$. Finally let $\sigma_0$ lie in the inertia subgroup with $\varepsilon(\sigma_0) = -1$. Then there exist $x_0, y \in T$ and $N \in \mathbb{N}$ with $x_0 \in P^0$, $y \in P$, $\rho(\sigma_0)y = y$, such that: $a x_0 + b y = 0$ with $a, b \in A$ (acting through their images in $\mathbb{T}$) forces $a = b = 0$; every $z \in P$ satisfies $p^N z = a x_0 + b y$ for some $a, b \in A$; every $z \in P^0$ satisfies $p^N z = a x_0$ for some $a \in A$; and every $z \in P$ with $\rho(\sigma_0)z = z$ satisfies $p^N z = b y$ for some $b \in A$.
--
--   This is the integral rank computation behind the ordinary filtration $0 \to P^0 \to P \to P/P^0 \to 0$ of the $p$-ordinary corner of the Tate module of $J_H(M)$ for $p \parallel M$: after inverting $p$ the corner becomes free of rank two over the corner ring on the pair $(x_0, y)$, with $x_0$ spanning the inertia eigenspace where inertia acts by the cyclotomic character and $y$ spanning the $\sigma_0$-fixed line, the integral statement being asserted only up to the bounded denominator $p^N$ and with no multiplicity-one or Gorenstein input. It is used in the construction of the characters of the decomposition group on the multiplicative part of the ordinary corner.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_adaptedLatticeBasis_inertiaEigenspace_cornerSubmodule_tateModule_jH_of_ordinary.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_adaptedLatticeBasis_inertiaEigenspace_cornerSubmodule_tateModule_jH_of_ordinary
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
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
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (P0 : Submodule 𝕋 (TateModule p (ModularCurve.JH M H)))
    (hP0 : ∀ x : TateModule p (ModularCurve.JH M H), x ∈ P0 ↔
      x ∈ IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀) ∧
        ∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ModularCurve.JH.tateGaloisRep M H p σ x =
          ((cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) • x)
    (σ₀ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hσ₀I : σ₀ ∈ Pl.inertiaSubgroupIn ℚ)
    (hεσ₀ : ((cyclotomicCharacter (AlgebraicClosure ℚ) p σ₀.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) = -1) :
    ∃ (x₀ y : TateModule p (ModularCurve.JH M H)) (N : ℕ),
      x₀ ∈ P0 ∧ y ∈ IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀) ∧
      ModularCurve.JH.tateGaloisRep M H p σ₀ y = y ∧
      (∀ a b : S'.CornerRing i₀, ((a : S'.CornerRing i₀) : 𝕋) • x₀ + ((b : S'.CornerRing i₀) : 𝕋) • y = 0 → a = 0 ∧ b = 0) ∧
      (∀ z ∈ IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀),
        ∃ a b : S'.CornerRing i₀, ((p : ℤ_[p]) ^ N) • z = ((a : S'.CornerRing i₀) : 𝕋) • x₀ + ((b : S'.CornerRing i₀) : 𝕋) • y) ∧
      (∀ z ∈ P0, ∃ a : S'.CornerRing i₀, ((p : ℤ_[p]) ^ N) • z = ((a : S'.CornerRing i₀) : 𝕋) • x₀) ∧
      (∀ z ∈ IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀), ModularCurve.JH.tateGaloisRep M H p σ₀ z = z →
        ∃ b : S'.CornerRing i₀, ((p : ℤ_[p]) ^ N) • z = ((b : S'.CornerRing i₀) : 𝕋) • y) := by sorry
