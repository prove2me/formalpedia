-- Prove2me | Theorems.Thm_HomotopyProxVM_prox_wellDefined
-- name    : HomotopyProxVM.prox_wellDefined
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:36:46.209783+00:00
-- url     : https://prove2.me/theorems/404ddd9f-2b39-436d-b7d9-9a8925d4608c
-- title:
--   (4), p.5 — $\operatorname{prox}^H_g(x)$ is well defined
-- statement:
--   Let $g:\mathbb R^p\to\mathbb R\cup\{+\infty\}$ be proper, closed and convex, and let $H$ be symmetric positive definite. For every $x\in\mathbb R^p$, the problem
--
--   $$
--   \operatorname{prox}^H_g(x):=\arg\min_{u\in\mathbb R^p}\Bigl\{g(u)+\tfrac12\|u-x\|_H^2\Bigr\}
--   $$
--
--   has exactly one solution.
--
--   The paper uses this tacitly; it is what makes the scheme (12) a well-defined map, and without it a run could fail to exist.
--
--   Differences from the source:
--   - encoding: g : ℝᵖ → ℝ ∪ {+∞} proper, closed, convex → g given by its domain D and its values on D; closed means the epigraph {(x,t) | x ∈ D, g x ≤ t} is closed; prox and argmin are sets of minimizers over D; reason: every proper function ℝᵖ → ℝ ∪ {+∞} has this form and the values off D are never read
-- source:
--   Tran-Dinh, Liang & Toh, A New Homotopy Proximal Variable-Metric Framework for Composite Convex Minimization, arXiv:1812.05243v1, §2.2, (4), p.5

import Mathlib
import Definitions.Def_OneStepProx_IsProperConvex
import Definitions.Def_OneStepProx_scaledProx
import Definitions.Def_HomotopyProxVM_IsClosedFn

namespace HomotopyProxVM

/-- Tran-Dinh, Liang & Toh, arXiv:1812.05243v1, §2.2, (4), p.5: for `H ∈ 𝕊ᵖ₊₊` and `g` proper, closed and convex, the operator
`prox^H_g(x) := argmin_u { g(u) + ½‖u − x‖²_H }` is well defined: the set of minimizers has
exactly one point.

**Formalization Note.** `H ≻ 0` is `Matrix.PosDef`, which includes symmetry. `g` is encoded by `D`
and its values on `D`; `prox` is the published set of minimizers `OneStepProx.scaledProx`. -/
theorem prox_wellDefined {p : ℕ} {H : Matrix (Fin p) (Fin p) ℝ} (hH : H.PosDef)
    {D : Set (EuclideanSpace ℝ (Fin p))} {g : EuclideanSpace ℝ (Fin p) → ℝ}
    (hg : OneStepProx.IsProperConvex D g) (hg_closed : IsClosedFn D g) (x : EuclideanSpace ℝ (Fin p)) :
    ∃! u, u ∈ OneStepProx.scaledProx H D g x := by sorry

end HomotopyProxVM
