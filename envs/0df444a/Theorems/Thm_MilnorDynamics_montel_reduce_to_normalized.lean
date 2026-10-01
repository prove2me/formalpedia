-- Prove2me | Theorems.Thm_MilnorDynamics_montel_reduce_to_normalized
-- name    : MilnorDynamics.montel_reduce_to_normalized
-- status  : Open
-- author  : @WillR
-- created : 2026-09-30T17:59:37.215771+00:00
-- url     : https://prove2.me/theorems/909f78ec-63c4-41d3-8ebf-c8d0a5155024
-- title:
--   Mobius normalisation - the general three-omitted-values case reduces to omitting 0, 1, infinity
-- statement:
--   **Mobius normalisation step.** Let $a,b,c\in\hat{\mathbb C}$ be three distinct points (possibly including $\infty$), let $U\subseteq\mathbb C$ be open, and let $\mathcal F$ be a family of holomorphic maps $U\to\hat{\mathbb C}$ omitting $a,b,c$. Then there is a family $\mathcal G$ of holomorphic maps $U\to\hat{\mathbb C}$ omitting the standard triple $0,1,\infty$, obtained by postcomposing each $f\in\mathcal F$ with a Mobius transformation of the sphere carrying $a\mapsto 0$, $b\mapsto 1$, $c\mapsto\infty$, and such that normality of $\mathcal G$ transfers back to normality of $\mathcal F$. This is the reduction at the start of Milnor's proof of Theorem 3.7: the Mobius group acts sharply 3-transitively on the sphere, so the general three-omitted-values statement is equivalent to the special case of the three omitted values $0,1,\infty$.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, ISBN 978-0-691-12488-9, Theorem 3.7, p. 36 (reduction of the three omitted values to 0, 1, infinity by a Mobius transformation), together with the sharp 3-transitivity of PSL(2, C) on the Riemann sphere.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem montel_reduce_to_normalized (a b c : OnePoint ℂ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (U : Set ℂ) (𝓕 : Set (ℂ → OnePoint ℂ))
    (h𝓕 : ∀ f ∈ 𝓕, IsHolomorphicOn U f ∧ ∀ z ∈ U, f z ≠ a ∧ f z ≠ b ∧ f z ≠ c) :
    ∃ 𝓖 : Set (ℂ → OnePoint ℂ),
      (∀ g ∈ 𝓖, IsHolomorphicOn U g ∧
        ∀ z ∈ U, g z ≠ ((0 : ℂ) : OnePoint ℂ) ∧ g z ≠ ((1 : ℂ) : OnePoint ℂ) ∧ g z ≠ ∞) ∧
      (IsNormalFamily U 𝓖 → IsNormalFamily U 𝓕) := by sorry

end MilnorDynamics
