-- Prove2me | Theorems.Thm_MilnorDynamics_exists_subseq_escapes_locally
-- name    : MilnorDynamics.exists_subseq_escapes_locally
-- status  : Open
-- author  : @WillR
-- created : 2026-10-01T03:56:22.778985+00:00
-- url     : https://prove2.me/theorems/21774ff2-13db-4e9d-910c-53e4420ec4f5
-- title:
--   Escape of an unbounded holomorphic family omitting two values: a subsequence tends to infinity locally uniformly
-- statement:
--   **Escape to infinity for a family omitting two values.** Let $U\subseteq\mathbb C$ be a connected open set and let $f_n:U\to\mathbb C\setminus\{0,1\}$ be holomorphic. If the family is not locally bounded - that is, if for some compact $K\subseteq U$ there is no constant bounding all the $|f_n|$ on $K$ - then some subsequence escapes to infinity locally uniformly on $U$:
--   $$\exists\ \varphi\ \text{strictly increasing},\qquad \forall K\subseteq U\ \text{compact},\ \forall R\in\mathbb R,\quad |f_{\varphi(n)}(z)|>R\ \text{ for all } z\in K \text{ and all large } n.$$
--
--   This is the real-valued analytic core of the escape step in Milnor's proof of Theorem 3.7. Together with the metric bridge `escapes_on_compacts_implies_diverges` it yields the statement that an unbounded family omitting two values has a subsequence diverging locally uniformly from the twice-punctured plane, which is the unbounded half of Montel's theorem. The content is the classical rigidity of holomorphic maps omitting two values: boundedness at a single point of a domain forces local boundedness, so a family that is unbounded anywhere must escape to infinity everywhere.
--
--   **Formalization Note** The statement is deliberately real-valued - no Riemann sphere, no chordal metric - so that the metric bookkeeping is confined to `escapes_on_compacts_implies_diverges`.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, Section 3 (the escape step in the proof of Montel's theorem); the underlying rigidity is Schottky's theorem / compactness of families omitting two values.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem exists_subseq_escapes_locally (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) U ∧ MapsTo (f n) U ({0, 1}ᶜ : Set ℂ))
    (hbdd : ∃ K ⊆ U, IsCompact K ∧
      ¬ (∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ K ⊆ U, IsCompact K → ∀ R : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K, R < ‖f (φ n) z‖ := by sorry

end MilnorDynamics
