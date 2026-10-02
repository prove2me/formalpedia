-- Prove2me | Theorems.Thm_HunterPDE_Compactness_halfSpace_trace
-- name    : HunterPDE.Compactness.halfSpace_trace
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T08:18:26.881692+00:00
-- url     : https://prove2.me/theorems/d2b61a62-fbd9-4c2f-b509-6556d8ad317b
-- title:
--   Theorem 3.44 — the trace operator W^{1,p}(ℝⁿ₊) → Lᵖ(∂ℝⁿ₊) and its kernel W^{1,p}_0(ℝⁿ₊)
-- statement:
--   For $1 \le p < \infty$ there is a bounded linear operator $T : W^{1,p}(\mathbb{R}^n_+) \to L^p(\partial\mathbb{R}^n_+)$ such that $(Tf)(x') = f(x', 0)$ for every $f \in C_c^\infty(\overline{\mathbb{R}}^n_+)$, and
--   $$\|Tf\|_{L^p(\mathbb{R}^{n-1})} \le C \, \|f\|_{W^{1,p}(\mathbb{R}^n_+)}$$
--   for some constant $C$ depending only on $p$. Furthermore, $f \in W^{1,p}_0(\mathbb{R}^n_+)$ if and only if $Tf = 0$.
--
--   The trace gives boundary values to Sobolev functions, which have no pointwise values on the null set $\partial\mathbb{R}^n_+$. It identifies $W^{1,p}_0$ as the space of functions that vanish on the boundary, which is the setting of Dirichlet problems.
--
--   **Formalization Note.** $n = m + 1$, and $\partial\mathbb{R}^n_+$ is identified with $\mathbb{R}^m$ through $x' \mapsto (x', 0)$ with Lebesgue measure. $C$ is quantified before $m$, as the page says it depends only on $p$. The page's last sentence reads "$f \in W^{k,p}_0(\mathbb{R}^n_+)$"; it is formalized with $k = 1$, the space $T$ acts on, since for $k \ge 2$ the converse fails (the notes observe on p. 73 that $W^{2,p} \cap W^{1,p}_0$ is the Dirichlet condition). $T$ is linear up to a.e. equality on $W^{1,p}(\mathbb{R}^n_+)$, and $(Tf)(x') = f(x',0)$ holds for a.e. $x'$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 72, Theorem 3.44

import Mathlib
import Definitions.Def_HunterPDE_Compactness_Sobolev
import Definitions.Def_HunterPDE_Compactness_HalfSpace

open MeasureTheory
open scoped ENNReal NNReal

namespace HunterPDE.Compactness

/-- Theorem 3.44 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 72: for `1 ≤ p < ∞` there is a
bounded linear operator `T : W^{1,p}(ℝⁿ₊) → Lᵖ(∂ℝⁿ₊)` such that `(Tf)(x′) = f(x′, 0)` for every
`f ∈ C_c^∞(ℝ̄ⁿ₊)` and `‖Tf‖_{Lᵖ(ℝⁿ⁻¹)} ≤ C ‖f‖_{W^{1,p}(ℝⁿ₊)}` for some constant `C` depending
only on `p`. Furthermore, `f ∈ W^{1,p}_0(ℝⁿ₊)` if and only if `Tf = 0`.
The dimension is `n = m + 1`, and `∂ℝⁿ₊` is identified with `ℝⁿ⁻¹ = ℝᵐ` through
`x′ ↦ (x′, 0)`; `C` is chosen before `m`, as the page says it depends only on `p`. The page's
"`f ∈ W^{k,p}_0(ℝⁿ₊)`" is read with `k = 1`, the space `T` acts on (for `k ≥ 2` the converse fails,
as the notes observe on p. 73). `T` is linear up to a.e. equality on `W^{1,p}(ℝⁿ₊)`. -/
theorem halfSpace_trace (p : ℝ≥0∞) (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ m : ℕ, ∃ T : (EuclideanSpace ℝ (Fin (m + 1)) → ℝ) → EuclideanSpace ℝ (Fin m) → ℝ,
      (∀ f g : EuclideanSpace ℝ (Fin (m + 1)) → ℝ,
        MemW 1 p (upperHalfSpace m) f → MemW 1 p (upperHalfSpace m) g → ∀ a b : ℝ,
          T (a • f + b • g) =ᵐ[volume] a • T f + b • T g) ∧
      (∀ f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ, MemW 1 p (upperHalfSpace m) f →
        MemLp (T f) p volume ∧
          eLpNorm (T f) p volume ≤ (C : ℝ≥0∞) * sobolevNorm 1 p (upperHalfSpace m) f) ∧
      (∀ f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ, IsSmoothCompactClosedHalfSpace f →
        T f =ᵐ[volume] fun x' => f (boundaryPoint x')) ∧
      (∀ f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ, MemW 1 p (upperHalfSpace m) f →
        (MemW0 1 p (upperHalfSpace m) f ↔ T f =ᵐ[volume] 0)) := by sorry

end HunterPDE.Compactness
