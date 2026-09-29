-- Prove2me | Theorems.Thm_MvPowerSeries_exists_algHom_apply_X_eq
-- name    : MvPowerSeries.exists_algHom_apply_X_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/1783c9c2-522c-5fb0-9a6e-546c3d9d8c1a
-- title:
--   Substitution of ideal elements into multivariate power series
-- statement:
--   Let $\sigma$ be a finite index type, let $\mathcal O$ and $A$ be commutative rings with $A$ an $\mathcal O$-algebra, and let $I$ be an ideal of $A$ such that $A$ is $I$-adically complete, i.e. `IsAdicComplete I A` holds (the $I$-adic filtration is Hausdorff: $\bigcap_n I^n = 0$, and every Cauchy sequence for that filtration has a limit). Let $a \colon \sigma \to A$ be a family of elements of $A$ with $a_i \in I$ for every $i \in \sigma$. Then there exists an $\mathcal O$-algebra homomorphism $\varphi \colon \mathcal O[[X_i : i \in \sigma]] \to A$ from the ring `MvPowerSeries σ 𝒪` of formal power series in the variables indexed by $\sigma$ into $A$ such that $\varphi(X_i) = a_i$ for all $i$, where $X_i$ denotes `MvPowerSeries.X i`. The assertion is pure existence: no uniqueness, no continuity and no compatibility with the filtrations beyond the displayed equations is claimed, and $A$ is not assumed Noetherian or local.
--
--   This is the substitution (evaluation) homomorphism $X_i \mapsto a_i$ for formal power series in finitely many variables, available because the substituted elements lie in an ideal with respect to which the target is complete; the typical instance is $I = \mathfrak m_A$ for a complete local $\mathcal O$-algebra $A$. It is used to construct power series presentations of complete algebras and to compute cotangent modules, for instance in [`AdicCompletion.exists_ringEquiv_mvPowerSeries_quotient_map_of_tensorProduct_of_flat`](thm.html#AdicCompletion.exists_ringEquiv_mvPowerSeries_quotient_map_of_tensorProduct_of_flat), [`AlgHom.bijective_and_exists_presentation_of_length_cotangent_le`](thm.html#AlgHom.bijective_and_exists_presentation_of_length_cotangent_le) and [`AlgHom.length_cotangent_eq_of_exists_presentation`](thm.html#AlgHom.length_cotangent_eq_of_exists_presentation).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPowerSeries_exists_algHom_apply_X_eq.lean

import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

theorem MvPowerSeries.exists_algHom_apply_X_eq {σ : Type u} {𝒪 : Type v} {A : Type w} [Finite σ] [CommRing 𝒪] [CommRing A] [Algebra 𝒪 A] (I : Ideal A) [IsAdicComplete I A] (a : σ → A) (ha : ∀ i, a i ∈ I) : ∃ φ : MvPowerSeries σ 𝒪 →ₐ[𝒪] A, ∀ i, φ (MvPowerSeries.X i) = a i := by sorry
