-- Prove2me | Theorems.Thm_MilnorDynamics_exists_subseq_tendsto_of_bounded_on_countable
-- name    : MilnorDynamics.exists_subseq_tendsto_of_bounded_on_countable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T00:37:57.951636+00:00
-- url     : https://prove2.me/theorems/6ece8fbf-7bc3-45c8-966b-81698d06fcd9
-- title:
--   Pointwise extraction on a countable set from a bounded family
-- statement:
--   **Pointwise extraction on a countable set.** Let $(D_k)_{k\in\mathbb N}$ be a sequence of complex numbers and let $(f_n)$ be a sequence of complex-valued functions such that for every $k$ the values $f_n(D_k)$ are bounded uniformly in $n$. Then there is a strictly increasing $\varphi$ and a sequence $(g_k)$ with
--
--   $$f_{\varphi(n)}(D_k)\longrightarrow g_k\qquad\text{for every }k.$$
--
--   Proof. For each $k$ choose $M_k$ bounding the sequence $n\mapsto f_n(D_k)$. Then each sequence is a sequence in the compact disc of radius $M_k$, so the corresponding sequence of coordinate functions is a sequence in the product of those compact discs. That product is compact by Tychonoff's theorem and the space of complex sequences is first countable, so the sequence has a convergent subsequence; coordinatewise convergence of that subsequence is the statement.
--
--   This is the diagonal-extraction seed used in the Arzela-Ascoli proof of Montel's theorem: it produces a subsequence converging on a countable set, which equicontinuity then upgrades to locally uniform convergence.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, Section 3; the classical diagonal extraction of a subsequence converging on a countable set.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem exists_subseq_tendsto_of_bounded_on_countable
    (D : ℕ → ℂ) (f : ℕ → ℂ → ℂ)
    (hb : ∀ k, ∃ M, ∀ n, ‖f n (D k)‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ g : ℕ → ℂ, ∀ k, Tendsto (fun n => f (φ n) (D k)) atTop (nhds (g k)) := by sorry

end MilnorDynamics
