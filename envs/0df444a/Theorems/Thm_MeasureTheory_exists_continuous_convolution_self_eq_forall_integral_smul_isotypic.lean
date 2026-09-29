-- Prove2me | Theorems.Thm_MeasureTheory_exists_continuous_convolution_self_eq_forall_integral_smul_isotypic
-- name    : MeasureTheory.exists_continuous_convolution_self_eq_forall_integral_smul_isotypic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/4feb3199-53fe-52a7-880f-5b778eed861b
-- title:
--   Continuous idempotent weight projecting onto ρ-isotypic vectors
-- statement:
--   Let $K$ be a compact Hausdorff topological group, equipped with its Borel $\sigma$-algebra, and let $\mu$ be a Haar probability measure on $K$; let $n$ be a natural number and $\rho : K \to M_n(\mathbb{C})$ a continuous multiplicative homomorphism into the multiplicative monoid of $n \times n$ complex matrices. The assertion is the existence of a function $e : K \to \mathbb{C}$ which is continuous, invariant under conjugation (so $e(lkl^{-1}) = e(k)$ for all $k, l$), satisfies $e(k^{-1}) = \overline{e(k)}$, and is idempotent for convolution against $\mu$, i.e. $\int_K e(l)\,e(l^{-1}k)\,d\mu(l) = e(k)$ for every $k$, and which has the following further property: for every complex Hilbert space $H$ (a complete inner product space over $\mathbb{C}$) and every multiplicative homomorphism $\pi : K \to (H \to_{L[\mathbb{C}]} H)$ into the continuous linear endomorphisms of $H$ such that each $\pi(k)$ is norm-preserving and the orbit maps $k \mapsto \pi(k)v$ are continuous, and for every continuous linear operator $A$ on $H$ given by $Av = \int_K e(k)\,\pi(k)v\,d\mu(k)$ for all $v$, one has: $A \circ A = A$; a vector $v$ satisfies $Av = v$ if and only if there exist $m \in \mathbb{N}$ and a continuous linear map $T : (\mathbb{C}^n)^m \to H$ intertwining the $m$-fold direct sum of $\rho$ (acting by $\mathrm{mulVec}$ in each coordinate) with $\pi$ such that $v$ lies in the range of $T$; and for every $v$, such an $m$ and $T$ exist with $Av$ in the range of $T$.
--
--   This is the construction of the $\rho$-isotypic projector of a compact group as an averaging operator against a continuous, conjugation-invariant, convolution-idempotent weight, with the resulting range characterised by finite multiples of $\rho$; the classical ingredients are the unitarisability and complete reducibility of finite-dimensional continuous representations together with Schur orthogonality of matrix coefficients. It is used to produce the idempotent cutting out the archimedean type in the cuspidal spectrum, via [`AutomorphicForm.CuspidalSpectrum.exists_idempotent_archTypeProjector`](thm.html#AutomorphicForm.CuspidalSpectrum.exists_idempotent_archTypeProjector).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_exists_continuous_convolution_self_eq_forall_integral_smul_isotypic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped ComplexConjugate

theorem MeasureTheory.exists_continuous_convolution_self_eq_forall_integral_smul_isotypic
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    {n : ℕ} (ρ : K →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ) :
    ∃ e : K → ℂ, Continuous e ∧ (∀ k l : K, e (l * k * l⁻¹) = e k) ∧ (∀ k : K, e k⁻¹ = conj (e k)) ∧
      (∀ k : K, ∫ l, e l * e (l⁻¹ * k) ∂μ = e k) ∧
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (π : K →* (H →L[ℂ] H)), (∀ (k : K) (v : H), ‖π k v‖ = ‖v‖) → (∀ v : H, Continuous fun k : K => π k v) →
        ∀ A : H →L[ℂ] H, (∀ v : H, A v = ∫ k, (e k) • (π k v) ∂μ) →
          A.comp A = A ∧
          (∀ v : H, A v = v ↔
            ∃ (m : ℕ) (T : (Fin m → (Fin n → ℂ)) →L[ℂ] H),
              (∀ (k : K) (x : Fin m → (Fin n → ℂ)), T (fun i => (ρ k).mulVec (x i)) = π k (T x)) ∧
              v ∈ LinearMap.range (T : (Fin m → (Fin n → ℂ)) →ₗ[ℂ] H)) ∧
          (∀ v : H, ∃ (m : ℕ) (T : (Fin m → (Fin n → ℂ)) →L[ℂ] H),
              (∀ (k : K) (x : Fin m → (Fin n → ℂ)), T (fun i => (ρ k).mulVec (x i)) = π k (T x)) ∧
              A v ∈ LinearMap.range (T : (Fin m → (Fin n → ℂ)) →ₗ[ℂ] H)) := by sorry
