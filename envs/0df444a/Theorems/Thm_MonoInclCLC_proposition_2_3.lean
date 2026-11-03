-- Prove2me | Theorems.Thm_MonoInclCLC_proposition_2_3
-- name    : MonoInclCLC.proposition_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:19:55.548908+00:00
-- url     : https://prove2.me/theorems/88909533-d32b-4b33-8ab5-31471f8399c6
-- title:
--   Proposition 2.3, p.5 — $\varphi(\cdot,x)$ is a continuous strictly increasing bijection onto $[0,\infty)$
-- statement:
--   Let $\mathcal H$ be a real Hilbert space and $A:\mathcal H\rightrightarrows\mathcal H$ a maximal monotone operator with $A^{-1}(0)=\{x:0\in Ax\}\neq\emptyset$. For an integer $p\ge 2$ let $\varphi(\lambda,x)=\lambda^{1/(p-1)}\|x-(I+\lambda A)^{-1}x\|$ for $\lambda>0$, and $\varphi(0,x)=0$. Fix $x\notin A^{-1}(0)$. Then the map $\lambda\mapsto\varphi(\lambda,x)$ is continuous and strictly increasing on $[0,+\infty)$, $\varphi(0,x)=0$, and
--   $$
--   \varphi(\lambda,x)\to+\infty\quad\text{as }\lambda\to+\infty.
--   $$
--   Consequently the feedback law $\Lambda_\theta(x)$ is well defined outside the zero set of $A$.
--
--   Differences from the source:
--   - encoding: the resolvent (I + λA)⁻¹ as an operator determined by A → a family J with IsResolvent l A (J l) for every l > 0; reason: for maximal monotone A such a map exists (Minty) and is unique (monotonicity), so no instance changes
-- source:
--   Lin, Jordan, Monotone Inclusions, Acceleration and Closed-Loop Control, arXiv:2111.08093v4, Proposition 2.3, p.5

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MonoInclCLC_phi

open InnerProductSpace ThreeOpSplitting.Convergence

namespace MonoInclCLC

/-- **Proposition 2.3** (Lin, Jordan, *Monotone Inclusions, Acceleration and Closed-Loop Control*, arXiv:2111.08093v4, Proposition 2.3, p.5): for `p ≥ 2` and fixed `x ∉ A⁻¹(0)`, the
mapping `ϕ(·, x)` is continuous and strictly increasing on `[0, +∞)`, `ϕ(0, x) = 0`, and
`ϕ(λ, x) → +∞` as `λ → +∞`.

**Formalization Note.** `J l` is the resolvent `(I + l A)⁻¹` for `l > 0`. `ϕ(·, x)` lives on `[0, +∞)`, hence `ContinuousOn` and `StrictMonoOn` on `Set.Ici 0`. -/
theorem proposition_2_3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H → Set H) (hA : IsMaximalMonotone A) (hzer : (zer A).Nonempty)
    (J : ℝ → H → H) (hJ : ∀ l : ℝ, 0 < l → IsResolvent l A (J l))
    (p : ℕ) (hp : 2 ≤ p)
    (x : H) (hx : x ∉ zer A) :
    ContinuousOn (fun l : ℝ => phi J p l x) (Set.Ici 0) ∧
      StrictMonoOn (fun l : ℝ => phi J p l x) (Set.Ici 0) ∧
      phi J p 0 x = 0 ∧
      Filter.Tendsto (fun l : ℝ => phi J p l x) Filter.atTop Filter.atTop := by sorry

end MonoInclCLC
