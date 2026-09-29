-- Prove2me | Theorems.Thm_MvPowerSeries_algHom_ext_of_apply_X_mem
-- name    : MvPowerSeries.algHom_ext_of_apply_X_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/b0edfae9-0c2c-5e84-baf6-b229567ce594
-- title:
--   Uniqueness of algebra maps from a power series ring
-- statement:
--   Let $\sigma$ be a finite type, $\mathcal O$ and $A$ commutative rings with $A$ an $\mathcal O$-algebra, and let $I \subseteq A$ be an ideal such that $A$ is $I$-adically Hausdorff, i.e. an element of $A$ congruent to $0$ modulo $I^n$ for every $n$ is $0$ (equivalently $\bigcap_{n} I^n = 0$). Let $\varphi, \psi \colon \mathcal O[[X_i : i \in \sigma]] \to A$ be two $\mathcal O$-algebra homomorphisms from the ring of multivariate formal power series in the variables indexed by $\sigma$. Assume that $\varphi(X_i) \in I$ for every $i \in \sigma$, and that $\varphi(X_i) = \psi(X_i)$ for every $i \in \sigma$. The conclusion is that $\varphi = \psi$ as $\mathcal O$-algebra homomorphisms. Note that the condition of landing in $I$ is imposed on $\varphi$ alone; by the agreement hypothesis it then holds for $\psi$ as well. No finiteness, Noetherian or completeness hypothesis on $A$ is required beyond the Hausdorff property of the $I$-adic topology.
--
--   This is the uniqueness half of the universal property of $\mathcal O[[X_1,\dots,X_n]]$ among $\mathcal O$-algebras equipped with an ideal defining a separated adic topology: a continuous $\mathcal O$-algebra map is determined by the images of the variables. It is used in the construction and comparison of power series presentations of deformation rings and Hecke algebras, and is cited in the project by results on adic completions, presentations of algebras over a residue field, and the computation of the length of a cotangent module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPowerSeries_algHom_ext_of_apply_X_mem.lean

import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

theorem MvPowerSeries.algHom_ext_of_apply_X_mem {σ : Type u} {𝒪 : Type v} {A : Type w} [Finite σ] [CommRing 𝒪] [CommRing A] [Algebra 𝒪 A] (I : Ideal A) [IsHausdorff I A] (φ ψ : MvPowerSeries σ 𝒪 →ₐ[𝒪] A) (hφ : ∀ i, φ (MvPowerSeries.X i) ∈ I) (h : ∀ i, φ (MvPowerSeries.X i) = ψ (MvPowerSeries.X i)) : φ = ψ := by sorry
