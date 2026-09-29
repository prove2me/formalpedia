-- Prove2me | Theorems.Thm_MeasureTheory_integral_mul_eq_integral_integral_subgroup_mul_mul_of_forall_integral_translate_eq_one
-- name    : MeasureTheory.integral_mul_eq_integral_integral_subgroup_mul_mul_of_forall_integral_translate_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/d9b1d9a5-cc86-5610-a488-c1bb4ce010ed
-- title:
--   Unfolding Sbackslash G through Tbackslash G with section functions
-- statement:
--   Let $G$ be a group carrying a topology making it a topological group, assumed locally compact and second countable, with its Borel $\sigma$-algebra, and let $\mu$ be a left Haar measure on $G$. Let $T \le G$ be a closed subgroup and $S \le T$ a closed subgroup of $G$ contained in $T$, each equipped with its Borel structure, and let $\tau$ on $T$ and $\tau_S$ on $S$ be Haar measures that are invariant under inversion. Let $F : G \to \mathbb{C}$ be measurable, bounded (there is a real $C$ with $\|F(x)\| \le C$ for all $x$), and left $S$-invariant, $F(sx) = F(x)$ for all $s \in S$, $x \in G$. Let $w_S : G \to \mathbb{R}$ be non-negative, measurable, of compact support, and satisfy $\int_S w_S(sx)\,d\tau_S(s) = 1$ for every $x$ with $F(x) \neq 0$; let $\beta : T \to \mathbb{R}$ be non-negative, measurable, of compact support, with $\int_S \beta(st)\,d\tau_S(s) = 1$ for every $t \in T$ (the element $s \in S$ being viewed in $T$ via $S \le T$); and let $W : G \to \mathbb{R}$ be non-negative, measurable, of compact support, with $\int_T W(tx)\,d\tau(t) = 1$ for every $x$ with $F(x) \neq 0$. Then $$\int_G F(x)\,w_S(x)\,d\mu(x) = \int_G \Bigl(\int_T F(tx)\,\beta(t)\,d\tau(t)\Bigr) W(x)\,d\mu(x),$$ the real-valued weights being coerced into $\mathbb{C}$.
--
--   This is the unfolding of an integral over $S\backslash G$ as an iterated integral over the fibration $S\backslash G \to T\backslash G$ with fibre $S\backslash T$, written with compactly supported section (partition-of-unity) functions in place of quotient measures: the left-hand side represents $\int_{S\backslash G} F$, the inner integral is the fibre average over $S\backslash T$, and the right-hand side represents the integral of that average over $T\backslash G$. It rests on the comparison of two $T$-sections for the same left $T$-invariant bounded function, [`MeasureTheory.integral_mul_eq_integral_mul_of_integral_subgroup_translate_eq_one`](thm.html#MeasureTheory.integral_mul_eq_integral_mul_of_integral_subgroup_translate_eq_one), and is used in the analysis of twisted orbital integrals, in [`AutomorphicForm.exists_pos_forall_tendsto_isTwistedOrbitalIntegralOn_mul_nhdsGT_conjAe_of_neg_of_inf_twistedCentralizer`](thm.html#AutomorphicForm.exists_pos_forall_tendsto_isTwistedOrbitalIntegralOn_mul_nhdsGT_conjAe_of_neg_of_inf_twistedCentralizer).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_integral_mul_eq_integral_integral_subgroup_mul_mul_of_forall_integral_translate_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.integral_mul_eq_integral_integral_subgroup_mul_mul_of_forall_integral_translate_eq_one
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (S : Subgroup G) (hS : IsClosed (S : Set G)) (hST : S ≤ T) [MeasurableSpace S] [BorelSpace S]
    (μ : Measure G) [μ.IsHaarMeasure]
    (τ : Measure T) [τ.IsHaarMeasure] [τ.IsInvInvariant]
    (τS : Measure S) [τS.IsHaarMeasure] [τS.IsInvInvariant]
    (F : G → ℂ) (hFm : Measurable F) (hFb : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C)
    (hFS : ∀ (s : S) (x : G), F ((s : G) * x) = F x)
    (wS : G → ℝ) (hwS0 : ∀ x, 0 ≤ wS x) (hwSm : Measurable wS) (hwSc : HasCompactSupport wS)
    (hwS1 : ∀ x : G, F x ≠ 0 → ∫ s : S, wS ((s : G) * x) ∂τS = 1)
    (β : T → ℝ) (hβ0 : ∀ t, 0 ≤ β t) (hβm : Measurable β) (hβc : HasCompactSupport β)
    (hβ1 : ∀ t : T, ∫ s : S, β (⟨(s : G), hST s.2⟩ * t) ∂τS = 1)
    (W : G → ℝ) (hW0 : ∀ x, 0 ≤ W x) (hWm : Measurable W) (hWc : HasCompactSupport W)
    (hW1 : ∀ x : G, F x ≠ 0 → ∫ t : T, W ((t : G) * x) ∂τ = 1) :
    ∫ x, F x * (wS x : ℂ) ∂μ = ∫ x, (∫ t : T, F ((t : G) * x) * (β t : ℂ) ∂τ) * (W x : ℂ) ∂μ := by sorry
