-- Prove2me | Theorems.Thm_GarrettFA_isQuasiComplete_testFunction
-- name    : GarrettFA.isQuasiComplete_testFunction
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T19:34:28.788514+00:00
-- url     : https://prove2.me/theorems/66acb52e-1196-4f1f-86ce-03cc9658627e
-- title:
--   §4 — the space of test functions is quasi-complete
-- statement:
--   For every $n$, the space $C_c^\infty(\mathbb R^n)$ of compactly supported smooth complex-valued functions on $\mathbb R^n$, with its usual LF-topology, is quasi-complete over $\mathbb C$.
--
--   **Formalization Note** The space is Mathlib's `TestFunction` space $\mathcal D(\mathbb R^n,\mathbb C)$ of smoothness order $\infty$ on the whole space, with Mathlib's topology: the finest locally convex topology for which all inclusions of the spaces $\mathcal D_K$ of test functions supported in a compact $K$ are continuous.
-- source:
--   Paul Garrett, *Completeness and quasi-completeness* (lecture notes, April 24, 2014), http://www.math.umn.edu/~garrett/m/fun/notes_2012-13/07d_quasi-completeness.pdf, p. 6, after Proposition 4.0.3 ("Thus, spaces of test functions are quasi-complete")

import Definitions.Def_GarrettFA_IsQuasiComplete

namespace GarrettFA
theorem isQuasiComplete_testFunction (n : ℕ) :
    IsQuasiComplete ℂ (TestFunction (⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))) ℂ ⊤) := by sorry
end GarrettFA
