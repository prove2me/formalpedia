-- Prove2me | Theorems.Thm_MeasureTheory_integrable_mul_of_integral_subgroup_translate_eq_one
-- name    : MeasureTheory.integrable_mul_of_integral_subgroup_translate_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/946bca74-8acd-5769-8255-ad5c6388b456
-- title:
--   Integrability of a bounded T-invariant function times a cut-off
-- statement:
--   Let $G$ be a group carrying a topology making it a topological group, assumed locally compact and second countable, and equipped with its Borel $\sigma$-algebra. Let $T$ be a subgroup of $G$ whose underlying set is closed, itself equipped with a measurable space structure that is the Borel structure of its topology. Let $\mu$ be a Haar measure on $G$, and let $\tau$ be a Haar measure on $T$ that is in addition invariant under $t \mapsto t^{-1}$. Let $F \colon G \to \mathbb{C}$ be measurable, bounded in the sense that there is a real $C$ with $\|F(x)\| \le C$ for all $x \in G$, and left $T$-invariant: $F(tx) = F(x)$ for all $t \in T$ and $x \in G$. Let $w \colon G \to \mathbb{R}$ satisfy the four conditions, bundled as a single conjunctive hypothesis, that $w \ge 0$ everywhere, that $w$ is measurable, that $w$ has compact support, and that $\int_T w(tx)\, d\tau(t) = 1$ for every $x \in G$ with $F(x) \ne 0$. Then the function $x \mapsto F(x) \cdot w(x)$, with $w(x)$ viewed in $\mathbb{C}$, is integrable with respect to $\mu$.
--
--   This is the integrability half of the standard unfolding device for integrals over a quotient $T \backslash G$: a compactly supported non-negative cut-off $w$ whose fibrewise $\tau$-integral equals $1$ on the support of $F$ converts a bounded $T$-invariant function on $G$ into a $\mu$-integrable function. It is used in the construction of orbital integrals at regular semisimple elements and in the companion statement that computes $\int_G F w \, d\mu$ for continuous data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_integrable_mul_of_integral_subgroup_translate_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.integrable_mul_of_integral_subgroup_translate_eq_one
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (μ : Measure G) [μ.IsHaarMeasure] (τ : Measure T) [τ.IsHaarMeasure] [τ.IsInvInvariant]
    (F : G → ℂ) (hFm : Measurable F) (hFb : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C)
    (hFT : ∀ (t : T) (x : G), F ((t : G) * x) = F x)
    (w : G → ℝ)
    (hw : (∀ x, 0 ≤ w x) ∧ Measurable w ∧ HasCompactSupport w ∧
      ∀ x, F x ≠ 0 → ∫ t : T, w ((t : G) * x) ∂τ = 1) :
    Integrable (fun x => F x * (w x : ℂ)) μ := by sorry
