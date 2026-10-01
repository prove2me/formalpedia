-- Prove2me | Theorems.Thm_MilnorDynamics_exists_subseq_tendsto_pointwise_of_locally_bounded
-- name    : MilnorDynamics.exists_subseq_tendsto_pointwise_of_locally_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T00:57:54.181812+00:00
-- url     : https://prove2.me/theorems/8ab1f455-0a33-40d8-9553-900001a9c059
-- title:
--   A locally bounded equicontinuous family has a pointwise convergent subsequence
-- statement:
--   **Pointwise extraction for a bounded equicontinuous family.** Let $U\subseteq\mathbb C$ be open and let $f_n$ be uniformly bounded and uniformly equicontinuous on every compact subset of $U$. Then some subsequence converges pointwise on all of $U$ to a continuous limit $g$.
--
--   Sketch. Enumerate a countable dense subset of $U$; the values of the family there are bounded, so a diagonal extraction gives a subsequence converging at every point of that dense set. Uniform equicontinuity then makes the extracted sequence Cauchy at every point of $U$, so a pointwise limit $g$ exists, and the equicontinuity modulus passes to the limit, which makes $g$ continuous.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, Section 3; the diagonal extraction of a subsequence in the Arzela-Ascoli proof.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem exists_subseq_tendsto_pointwise_of_locally_bounded (U : Set ℂ) (hU : IsOpen U)
    (f : ℕ → ℂ → ℂ)
    (hb : ∀ K ⊆ U, IsCompact K → ∃ M, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M)
    (hmod : ∀ K ⊆ U, IsCompact K → ∀ ε > 0, ∃ δ > 0, ∀ n, ∀ x ∈ K, ∀ y ∈ K,
      ‖x - y‖ < δ → ‖f n x - f n y‖ < ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℂ → ℂ, ContinuousOn g U ∧
      ∀ x ∈ U, Tendsto (fun n => f (φ n) x) atTop (nhds (g x)) := by sorry

end MilnorDynamics
