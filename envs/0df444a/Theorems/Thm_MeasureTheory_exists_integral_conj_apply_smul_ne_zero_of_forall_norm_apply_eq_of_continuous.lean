-- Prove2me | Theorems.Thm_MeasureTheory_exists_integral_conj_apply_smul_ne_zero_of_forall_norm_apply_eq_of_continuous
-- name    : MeasureTheory.exists_integral_conj_apply_smul_ne_zero_of_forall_norm_apply_eq_of_continuous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/a416e190-b44e-591c-b77b-9e8af0b68d6e
-- title:
--   Non-vanishing matrix coefficient mean for isometric representations
-- statement:
--   Let $K$ be a compact Hausdorff topological group, carrying a Borel measurable structure compatible with its topology, and let $\mu$ be a Haar measure on $K$ which is a probability measure. Let $H$ be a complex Hilbert space (a complete normed additive commutative group with a complex inner product structure), and let $\pi : K \to (H \to_{L[\mathbb{C}]} H)$ be a monoid homomorphism into the continuous $\mathbb{C}$-linear endomorphisms of $H$, subject to two hypotheses: $\|\pi(k)v\| = \|v\|$ for all $k \in K$ and $v \in H$ (isometry), and $k \mapsto \pi(k)v$ is continuous for every $v \in H$ (strong continuity). Assume further that the continuous finite-dimensional matrix representations of $K$ separate $1$ from every other point: for every $k \neq 1$ there exist $n \in \mathbb{N}$ and a monoid homomorphism $\rho : K \to M_n(\mathbb{C})$ with $\rho$ continuous and $\rho(k) \neq 1$. Then for every $v \in H$ with $v \neq 0$ there exist $n \in \mathbb{N}$, a monoid homomorphism $\rho : K \to M_n(\mathbb{C})$ and indices $i, j \in \{0,\dots,n-1\}$ such that $\rho$ is continuous and the $H$-valued Bochner integral $\int_K \overline{\rho(k)_{ij}} \cdot \pi(k)v \, d\mu(k)$ is non-zero.
--
--   This is the consequence of the Peter–Weyl theorem needed by users of the theory — that a non-zero vector in a strongly continuous isometric representation of a compact group has a non-vanishing matrix-coefficient mean, hence a non-zero $K$-finite projection — formulated for an arbitrary compact group with the separation of points by continuous finite-dimensional representations taken as a hypothesis. It is applied in the analysis of the cuspidal spectrum, to produce a vector in the archimedean cut submodule pairing non-trivially with a given non-zero cuspidal vector; the proof invokes the vanishing criterion [`ContinuousMap.ae_eq_zero_of_forall_mem_starSubalgebra_integral_mul_eq_zero`](thm.html#ContinuousMap.ae_eq_zero_of_forall_mem_starSubalgebra_integral_mul_eq_zero), a Stone–Weierstrass argument for star subalgebras of $C(X,\mathbb{C})$ that separate points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_exists_integral_conj_apply_smul_ne_zero_of_forall_norm_apply_eq_of_continuous.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped ComplexConjugate

theorem MeasureTheory.exists_integral_conj_apply_smul_ne_zero_of_forall_norm_apply_eq_of_continuous
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : K →* (H →L[ℂ] H))
    (hπn : ∀ (k : K) (v : H), ‖π k v‖ = ‖v‖)
    (hπc : ∀ v : H, Continuous fun k : K => π k v)
    (hsep : ∀ k : K, k ≠ 1 →
      ∃ (n : ℕ) (ρ : K →* Matrix (Fin n) (Fin n) ℂ), Continuous ρ ∧ ρ k ≠ 1)
    (v : H) (hv : v ≠ 0) :
    ∃ (n : ℕ) (ρ : K →* Matrix (Fin n) (Fin n) ℂ) (i j : Fin n), Continuous ρ ∧
      ∫ k, (conj ((ρ k) i j)) • (π k v) ∂μ ≠ 0 := by sorry
