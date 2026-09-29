-- Prove2me | Theorems.Thm_MeasureTheory_exists_section_integral_mul_eq_sum_div_of_forall_eq_of_forall_exists
-- name    : MeasureTheory.exists_section_integral_mul_eq_sum_div_of_forall_eq_of_forall_exists
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/0f3470c7-c523-5258-808d-6adf5e2568e0
-- title:
--   Existence of a section weight for finitely many T–U double cosets
-- statement:
--   Let $G$ be a topological group with a Borel measurable structure compatible with its topology, and let $\mu$ be a left-invariant measure on $G$. Let $U\subseteq G$ be open and compact with $\mu(U)\neq\infty$, containing $1$, closed under multiplication ($a,b\in U\Rightarrow ab\in U$) and under inversion. Let $T\le G$ be a subgroup whose underlying set is closed, equipped with a Borel measurable structure and a right-invariant measure $\tau$ which is finite on compact sets and gives every non-empty open set positive mass. Let $\psi\colon G\to\mathbb C$ satisfy $\psi(txu)=\psi(x)$ for all $t\in T$, $x\in G$, $u\in U$, and let $S\subseteq G$ be a finite set such that (i) for $s,s'\in S$, $t\in T$ and $u\in U$, $s'=tsu$ forces $s'=s$, and (ii) every $x$ with $\psi(x)\neq 0$ can be written $x=tsu$ with $s\in S$, $t\in T$, $u\in U$. The conclusion asserts the existence of a function $w\colon G\to\mathbb R$ which is everywhere non-negative, measurable and of compact support, such that $\int_T w(tx)\,d\tau(t)=1$ for every $x$ with $\psi(x)\neq 0$, and such that
--   $$\int_G \psi(x)\,w(x)\,d\mu(x)=\sum_{s\in S}\psi(s)\,\frac{\mu(U)}{\tau\bigl(\{t\in T: s^{-1}ts\in U\}\bigr)},$$
--   the masses being read as real numbers and the sum formed in $\mathbb C$.
--
--   This is the double-coset (level-$U$) section-function construction underlying the coset formula for orbital integrals: $w$ is a weight whose $T$-integral along each orbit is $1$, so that integrating $\psi$ against $w$ over $G$ collapses to a finite sum over the chosen double-coset representatives, with the $\tau$-mass of $T\cap sUs^{-1}$ in the denominators. It is used in the passage from an integral over $G$ to a finite sum of orbital integral contributions, via [`AutomorphicForm.exists_finset_isOrbitalIntegral_sum_mul_div_of_forall_mul_eq_of_isOpen`](thm.html#AutomorphicForm.exists_finset_isOrbitalIntegral_sum_mul_div_of_forall_mul_eq_of_isOpen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_exists_section_integral_mul_eq_sum_div_of_forall_eq_of_forall_exists.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_section_integral_mul_eq_sum_div_of_forall_eq_of_forall_exists
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (U : Set G)
    (hUo : IsOpen U) (hUc : IsCompact U) (hμUtop : μ U ≠ ⊤)
    (h1U : (1 : G) ∈ U) (hUmul : ∀ a ∈ U, ∀ b ∈ U, a * b ∈ U) (hUinv : ∀ a ∈ U, a⁻¹ ∈ U)
    (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (τ : Measure T) [τ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts τ] [τ.IsOpenPosMeasure]
    (ψ : G → ℂ) (hψ : ∀ t ∈ T, ∀ x : G, ∀ u ∈ U, ψ (t * x * u) = ψ x)
    (S : Finset G)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ T, ∀ u ∈ U, s' = t * s * u → s' = s)
    (hcov : ∀ x, ψ x ≠ 0 → ∃ s ∈ S, ∃ t ∈ T, ∃ u ∈ U, x = t * s * u) :
    ∃ w : G → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable w ∧ HasCompactSupport w ∧
      (∀ x, ψ x ≠ 0 → ∫ t : T, w ((t : G) * x) ∂τ = 1) ∧
      ∫ x, ψ x * (w x : ℂ) ∂μ =
        ∑ s ∈ S, ψ s * ((μ U).toReal : ℂ) / ((τ {t : T | s⁻¹ * (t : G) * s ∈ U}).toReal : ℂ) := by sorry
