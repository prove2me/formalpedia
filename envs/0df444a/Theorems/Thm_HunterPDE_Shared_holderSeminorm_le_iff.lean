-- Prove2me | Theorems.Thm_HunterPDE_Shared_holderSeminorm_le_iff
-- name    : HunterPDE.Shared.holderSeminorm_le_iff
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T16:28:13.383886+00:00
-- url     : https://prove2.me/theorems/5722cb08-367d-4bcc-bfc0-58cb099373bb
-- title:
--   Hölder seminorm bounds are equivalent to pointwise increment bounds
-- statement:
--   Let $\alpha$ be any real exponent, $\Omega\subseteq\mathbb R^n$ any set, $f:\mathbb R^n\to\mathbb R$ any function, and $C\ge0$ a finite constant. Then
--
--   $$[f]_{\alpha,\Omega}\le C\quad\Longleftrightarrow\quad |f(x)-f(y)|\le C\|x-y\|^\alpha\text{ for all distinct }x,y\in\Omega.$$
--
--   This characterization connects the extended nonnegative Hölder seminorm to finite pointwise increment bounds. It requires no regularity or boundedness assumptions and applies to every real exponent.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch1.pdf, printed p. 2, Definition 1.1, Eq. (1.1): direct characterization of the defining supremum.

import Definitions.Def_HunterPDE_Shared_HolderSeminorm
import Mathlib.Tactic.Positivity
open scoped ENNReal NNReal

theorem HunterPDE.Shared.holderSeminorm_le_iff (n : ℕ) (α : ℝ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (C : ℝ≥0) :
    HunterPDE.Shared.holderSeminorm α Ω f ≤ (C : ℝ≥0∞) ↔
      ∀ x ∈ Ω, ∀ y ∈ Ω, x ≠ y → |f x - f y| ≤ (C : ℝ) * ‖x - y‖ ^ α := by sorry
