-- Prove2me | Theorems.Thm_MilnorDynamics_montel_three_omitted_values
-- name    : MilnorDynamics.montel_three_omitted_values
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T12:08:58.198514+00:00
-- url     : https://prove2.me/theorems/90623051-0393-484c-96f1-2f271789181a
-- title:
--   Theorem 3.7 (Montel) — holomorphic maps omitting three values form a normal family
-- statement:
--   Let $U\subseteq\mathbb C$ be a domain (a nonempty connected open set), and let $\mathcal F$ be a family of holomorphic maps from $U$ to the Riemann sphere $\hat{\mathbb C}=\mathbb C\cup\{\infty\}$ which omit three different values: there are distinct points $a,b,c\in\hat{\mathbb C}$ such that
--
--   $$f(U)\subseteq\hat{\mathbb C}\setminus\{a,b,c\}\qquad\text{for every } f\in\mathcal F.$$
--
--   Then $\mathcal F$ is a **normal family**: every sequence in $\mathcal F$ has a subsequence which converges locally uniformly on $U$, with respect to the spherical (chordal) metric, to a continuous limit map $U\to\hat{\mathbb C}$.
--
--   Montel's theorem is the basic tool of the whole theory of iteration: it is what makes the Fatou/Julia dichotomy effective, and it is used in the proofs that the Julia set is nonempty, that iterated preimages are dense in it, and that repelling cycles are dense in it.
--
--   **Formalization Note** Milnor states the theorem for an arbitrary Riemann surface $S$; here the source is a planar domain $U\subseteq\mathbb C$, which is the case used for Fatou sets (normality is a local property, Milnor's Problem 3-e). Maps into $\hat{\mathbb C}$ are represented as functions $\mathbb C\to\hat{\mathbb C}$ that are holomorphic on $U$ in the chart-wise sense of `IsHolomorphicOn`; values outside $U$ are irrelevant.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, ISBN 978-0-691-12488-9, §3, p. 36, Theorem 3.7 (Montel), specialised to a Riemann surface S that is a domain in C

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem montel_three_omitted_values (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (a b c : OnePoint ℂ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (𝓕 : Set (ℂ → OnePoint ℂ))
    (h𝓕 : ∀ f ∈ 𝓕, IsHolomorphicOn U f ∧ ∀ z ∈ U, f z ≠ a ∧ f z ≠ b ∧ f z ≠ c) :
    IsNormalFamily U 𝓕 := by sorry

end MilnorDynamics
