-- Prove2me | Theorems.Thm_MeasureTheory_Measure_exists_eq_smul_map_smul_of_forall_map_smul_eq_of_isCompact_stabilizer
-- name    : MeasureTheory.Measure.exists_eq_smul_map_smul_of_forall_map_smul_eq_of_isCompact_stabilizer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/d57dad0f-b76a-5600-900c-95918b6d1964
-- title:
--   Uniqueness of invariant measures on homogeneous spaces with compact stabilisers
-- statement:
--   Let $L$ be a group carrying a topology making it a topological group which is locally compact and second countable, equipped with its Borel $\sigma$-algebra, and let $\mu_L$ be a Haar measure on $L$. Let $X$ be a locally compact Hausdorff space with its Borel $\sigma$-algebra, equipped with a continuous action of $L$ which is pretransitive (any point of $X$ can be moved to any other by some element of $L$). Fix $x_0 \in X$ whose stabiliser $\{g \in L : g \cdot x_0 = x_0\}$ is a compact subset of $L$. Let $\sigma$ be a measure on $X$ which is finite on compact sets and invariant under the action, in the sense that the pushforward of $\sigma$ along $x \mapsto g \cdot x$ equals $\sigma$ for every $g \in L$. Then there exists a constant $c \in [0,\infty]$ with $c \neq \infty$ such that $\sigma = c \cdot (g \mapsto g \cdot x_0)_{*}\mu_L$, the pushforward of $\mu_L$ along the orbit map at $x_0$ scaled by $c$. Note that $c$ is only asserted to be a finite element of $\mathbb{R}_{\geq 0}^{\infty}$; no positivity is claimed.
--
--   This is the uniqueness part of Weil's theorem on invariant measures on a homogeneous space $L/M$ in the case of compact isotropy $M$, where no modular-function condition intervenes because $\Delta_L|_M = \Delta_M = 1$. It is used in the adelic integration theory underlying the trace-formula and Iwasawa-decomposition computations, being invoked to compare an invariant measure on an adelic homogeneous space with the image of Haar measure on the group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_Measure_exists_eq_smul_map_smul_of_forall_map_smul_eq_of_isCompact_stabilizer.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

theorem MeasureTheory.Measure.exists_eq_smul_map_smul_of_forall_map_smul_eq_of_isCompact_stabilizer
    {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [LocallyCompactSpace L]
    [SecondCountableTopology L] [MeasurableSpace L] [BorelSpace L]
    (μL : Measure L) [μL.IsHaarMeasure]
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [MulAction L X] [ContinuousSMul L X] [MulAction.IsPretransitive L X]
    (x₀ : X) (hx₀ : IsCompact (MulAction.stabilizer L x₀ : Set L))
    (σ : Measure X) [IsFiniteMeasureOnCompacts σ]
    (hσ : ∀ g : L, σ.map (fun x : X => g • x) = σ) :
    ∃ c : ℝ≥0∞, c ≠ ∞ ∧ σ = c • μL.map (fun g : L => g • x₀) := by sorry
