-- Prove2me | Theorems.Thm_HunterPDE_Compactness_halfSpace_density
-- name    : HunterPDE.Compactness.halfSpace_density
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T08:09:23.731975+00:00
-- url     : https://prove2.me/theorems/72bbacba-66b7-47a8-9e4a-6f648269344a
-- title:
--   Theorem 3.42 — C_c^∞(ℝ̄ⁿ₊) is dense in W^{k,p}(ℝⁿ₊)
-- statement:
--   The space $C_c^\infty(\overline{\mathbb{R}}^n_+)$ of smooth functions is dense in $W^{k,p}(\mathbb{R}^n_+)$: for every $f \in W^{k,p}(\mathbb{R}^n_+)$ and $\varepsilon > 0$ there is $\phi \in C_c^\infty(\overline{\mathbb{R}}^n_+)$ with
--   $$\|f - \phi\|_{W^{k,p}(\mathbb{R}^n_+)} < \varepsilon.$$
--
--   The approximants are smooth up to the boundary but need not vanish there. This is what makes the trace map (Theorem 3.44) definable by continuity.
--
--   **Formalization Note.** The dimension is $n = m + 1$, $k \in \mathbb{N}$, and $1 \le p < \infty$. The page gives no range of $p$; this is the range of the whole-space analogue, Theorem 3.24, and density fails for $p = \infty$. $\overline{\mathbb{R}}^n_+$ is the closed half-space, not the open one.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 72, Theorem 3.42

import Mathlib
import Definitions.Def_HunterPDE_Compactness_Sobolev
import Definitions.Def_HunterPDE_Compactness_HalfSpace

open MeasureTheory
open scoped ENNReal

namespace HunterPDE.Compactness

/-- Theorem 3.42 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 72: the space `C_c^∞(ℝ̄ⁿ₊)`
of smooth functions (smooth up to the boundary, vanishing on `ℝ̄ⁿ₊` outside a compact set, not
necessarily zero on `∂ℝⁿ₊`) is dense in `W^{k,p}(ℝⁿ₊)`: every `f ∈ W^{k,p}(ℝⁿ₊)` is approximated
in the `W^{k,p}(ℝⁿ₊)` norm by such functions. Dimension `n = m + 1`, `k ∈ ℕ`, and `1 ≤ p < ∞`
(the range of the whole-space analogue, Theorem 3.24; density fails for `p = ∞`). -/
theorem halfSpace_density (m k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ) (hf : MemW k p (upperHalfSpace m) f)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ φ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ, IsSmoothCompactClosedHalfSpace φ ∧
      sobolevNorm k p (upperHalfSpace m) (f - φ) < ε := by sorry

end HunterPDE.Compactness
