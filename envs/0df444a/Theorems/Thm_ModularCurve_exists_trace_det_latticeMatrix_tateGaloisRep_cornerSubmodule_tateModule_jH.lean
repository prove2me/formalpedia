-- Prove2me | Theorems.Thm_ModularCurve_exists_trace_det_latticeMatrix_tateGaloisRep_cornerSubmodule_tateModule_jH
-- name    : ModularCurve.exists_trace_det_latticeMatrix_tateGaloisRep_cornerSubmodule_tateModule_jH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/4b297560-c2ef-5158-820f-45c2760f28b1
-- title:
--   Trace and determinant of Galois on a corner of Tₚ(J_H)
-- statement:
--   Fix a nonzero integer $M$, a prime $p$, a subgroup $H\le(\mathbb{Z}/M)^\times$ and a finite set $S$ of naturals, and assume [`ModularCurve.HeckeDiamondInputsHAll M H`](def/ModularCurve_XHOperators.html#L113), i.e. the Hecke inputs along every prime $\ell$ for $X_H(M)$ over $\overline{\mathbb{Q}}$ together with, for each $d\in(\mathbb{Z}/M)^\times$, a diamond automorphism of the base-changed function field. Let $\mathbb{T}$ be a commutative $\mathbb{Z}_p$-algebra acting on the $p$-adic Tate module $T=T_p(J_H(M))$ (compatible systems of $p^n$-torsion classes in the degree-zero divisor class group of $\overline{\mathbb{Q}}\cdot F(\Gamma_H(M))$) compatibly with $\mathbb{Z}_p$, faithfully (an element killing all of $T$ is $0$), and let $\mathrm{op}$ send each generator $g\in$ [`CohCarrier.Gen M S`](def/CohCarrier_Inst.html#L13) (the symbols $T_\ell$, $U_q$, $\langle d\rangle$) to an element of $\mathbb{T}$ acting as `tateGenOpH`, with $\mathbb{T}=\mathbb{Z}_p[\mathrm{op}(g)]$. Let $S'$ be an idempotent splitting of $\mathbb{T}$ (complete orthogonal idempotents $e_i$ matched with all maximal ideals) and $i_0$ an index; write $R=$ `CornerRing` $i_0$, the corner ring of $e_{i_0}$, and $P=e_{i_0}T$. Then there are functions $\mathrm{tr},\mathrm{dt}:\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})\to R$ and intermediate fields $L_n\subseteq\overline{\mathbb{Q}}$ with: $\mathrm{tr}\,1=2$, $\mathrm{dt}\,1=1$; both conjugation invariant; $\mathrm{dt}$ multiplicative; $(\mathrm{tr}\,\sigma)^2=\mathrm{tr}(\sigma^2)+2\,\mathrm{dt}\,\sigma$; for all $\sigma$ and $x\in P$, $\rho(\sigma)^2x-\mathrm{tr}\,\sigma\cdot\rho(\sigma)x+\mathrm{dt}\,\sigma\cdot x=0$, where $\rho$ is the Galois action on $T$; each $L_n$ finite over $\mathbb{Q}$ with every $\sigma$ fixing $L_n$ pointwise satisfying $\rho(\sigma)x\in x+p^nT$ for all $x$ and $\mathrm{tr}(\sigma\tau)\equiv\mathrm{tr}\,\tau$, $\mathrm{dt}(\sigma\tau)\equiv\mathrm{dt}\,\tau$ modulo $p^nR$; for every prime $\ell\notin S$ with $\ell\nmid M$, $\ell\ne p$, every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $\ell$ a nonunit of $A$ and every $\sigma$ acting as $x\mapsto x^\ell$ on the residue field of $A$ from its decomposition group, the corner images satisfy $\langle\ell\rangle\,\mathrm{tr}\,\sigma=T_\ell$ and $\langle\ell\rangle\,\mathrm{dt}\,\sigma=\ell$; and finally, for $x,y\in P$ with $ax+by=0\Rightarrow a=b=0$ over $R$ and $N$ with $p^NP\subseteq Rx+Ry$, any $a,b,c,d\in R$ with $p^N\rho(\sigma)x=ax+cy$ and $p^N\rho(\sigma)y=bx+dy$ satisfy $p^N\mathrm{tr}\,\sigma=a+d$ and $p^{2N}\mathrm{dt}\,\sigma=ad-bc$.
--
--   This packages the Eichler–Shimura relation on the $p$-adic Tate module of $J_H(M)$ into trace and determinant functions for the Galois action on a local (corner) factor cut out by an idempotent of the Hecke algebra: a quadratic relation with continuous, conjugation-invariant coefficients whose values at Frobenius elements are given by $T_\ell$ and $\ell$ after multiplication by the diamond operator $\langle\ell\rangle$, together with the compatibility of $\mathrm{tr}$ and $\mathrm{dt}$ with any pair of elements spanning the corner factor up to $p$-power denominators. It is used in the construction of the ordinary filtration and parabolic homomorphisms attached to a non-Eisenstein maximal ideal of the Hecke algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_trace_det_latticeMatrix_tateGaloisRep_cornerSubmodule_tateModule_jH.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_trace_det_latticeMatrix_tateGaloisRep_cornerSubmodule_tateModule_jH
    (M p : ℕ) [NeZero M] [Fact p.Prime] (H : Subgroup (ZMod M)ˣ) (S : Finset ℕ)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 (TateModule p (ModularCurve.JH M H))]
    [IsScalarTower ℤ_[p] 𝕋 (TateModule p (ModularCurve.JH M H))]
    (hfaith : ∀ t : 𝕋, (∀ x : TateModule p (ModularCurve.JH M H), t • x = 0) → t = 0)
    (op : CohCarrier.Gen M ↑S → 𝕋)
    (hop : ∀ (g : CohCarrier.Gen M ↑S) (x : TateModule p (ModularCurve.JH M H)),
      op g • x = ModularCurve.tateGenOpH M H ↑S p g x)
    (hgen : Algebra.adjoin ℤ_[p] (Set.range op) = ⊤)
    (S' : IharaLemma.IdempotentSplitting 𝕋) (i₀ : Fin S'.n) :
    ∃ (tr dt : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → S'.CornerRing i₀)
      (L : ℕ → IntermediateField ℚ (AlgebraicClosure ℚ)),

      tr 1 = 2 ∧ dt 1 = 1 ∧

      (∀ σ τ, tr (σ * τ * σ⁻¹) = tr τ) ∧ (∀ σ τ, dt (σ * τ * σ⁻¹) = dt τ) ∧
      (∀ σ τ, dt (σ * τ) = dt σ * dt τ) ∧

      (∀ σ, tr σ * tr σ = tr (σ * σ) + 2 * dt σ) ∧
      (∀ σ, ∀ x ∈ IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀),
        ModularCurve.JH.tateGaloisRep M H p σ (ModularCurve.JH.tateGaloisRep M H p σ x)
          - ((tr σ : S'.CornerRing i₀) : 𝕋) • ModularCurve.JH.tateGaloisRep M H p σ x
          + ((dt σ : S'.CornerRing i₀) : 𝕋) • x = 0) ∧

      (∀ n : ℕ, FiniteDimensional ℚ (L n) ∧
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L n, σ x = x) →
          (∀ x : TateModule p (ModularCurve.JH M H), ∃ y : TateModule p (ModularCurve.JH M H),
            ModularCurve.JH.tateGaloisRep M H p σ x = x + ((p : ℤ_[p]) ^ n) • y) ∧
          (∀ τ, ∃ b : S'.CornerRing i₀, tr (σ * τ) = tr τ + (p : S'.CornerRing i₀) ^ n * b) ∧
          (∀ τ, ∃ b : S'.CornerRing i₀, dt (σ * τ) = dt τ + (p : S'.CornerRing i₀) ^ n * b)) ∧

      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M), ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            S'.toCornerRing i₀ (op (CohCarrier.Gen.dia
                (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)))) * tr σ =
              S'.toCornerRing i₀ (op (CohCarrier.Gen.T ℓ hℓ hℓS hℓM)) ∧
            S'.toCornerRing i₀ (op (CohCarrier.Gen.dia
                (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)))) * dt σ =
              (ℓ : S'.CornerRing i₀)) ∧

      (∀ x ∈ IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀),
        ∀ y ∈ IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀),
          (∀ a b : S'.CornerRing i₀,
            ((a : S'.CornerRing i₀) : 𝕋) • x + ((b : S'.CornerRing i₀) : 𝕋) • y = 0 → a = 0 ∧ b = 0) →
          ∀ N : ℕ,
            (∀ z ∈ IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀),
              ∃ a b : S'.CornerRing i₀, ((p : ℤ_[p]) ^ N) • z =
                ((a : S'.CornerRing i₀) : 𝕋) • x + ((b : S'.CornerRing i₀) : 𝕋) • y) →
            ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a b c d : S'.CornerRing i₀),
              ((p : ℤ_[p]) ^ N) • ModularCurve.JH.tateGaloisRep M H p σ x =
                ((a : S'.CornerRing i₀) : 𝕋) • x + ((c : S'.CornerRing i₀) : 𝕋) • y →
              ((p : ℤ_[p]) ^ N) • ModularCurve.JH.tateGaloisRep M H p σ y =
                ((b : S'.CornerRing i₀) : 𝕋) • x + ((d : S'.CornerRing i₀) : 𝕋) • y →
              (p : S'.CornerRing i₀) ^ N * tr σ = a + d ∧
              (p : S'.CornerRing i₀) ^ (2 * N) * dt σ = a * d - b * c) := by sorry
