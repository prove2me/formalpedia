-- Prove2me | Theorems.Thm_MonoIncExtrap_sum_maximal_monotone
-- name    : MonoIncExtrap.sum_maximal_monotone
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:29:10.264267+00:00
-- url     : https://prove2.me/theorems/ad62d058-344e-4e12-9276-03cd9f927b1d
-- title:
--   §1, p.2 — $F+B$ is maximal monotone
-- statement:
--   Let $B:\mathbb R^n\rightrightarrows\mathbb R^n$ and $F$ satisfy the standing assumptions of problem (1): $B$ is maximal monotone with nonempty domain, and $F$ is monotone and locally Lipschitz on $\mathrm{cl}(\mathrm{dom}\,B)$, with $F+B$ monotone with parameter $\mu\ge0$. Then
--   $$
--   F+B\text{ is maximal monotone.}
--   $$
--
--   This is what makes the proximal subproblems of Algorithm 2 solvable: the resolvent $(I+\rho(F+B))^{-1}$ is defined on all of $\mathbb R^n$. The paper cites it from Monteiro and Svaiter (2011), Proposition A.1.
--
--   Differences from the source:
--   - encoding: $F$ is a point-valued operator on $\mathrm{cl}(\mathrm{dom}\,B)$ → a total map on $\mathbb R^n$, constrained only on $\mathrm{cl}(\mathrm{dom}\,B)$; reason: values of $F$ elsewhere never enter $F+B$ or a run, since iterates lie in $\mathrm{dom}\,B$
-- source:
--   Lu & Mei, Primal-dual extrapolation methods for monotone inclusions under local Lipschitz continuity, arXiv:2206.00973v3, §1, p.2, "F + B is maximal monotone (e.g., see [16, Proposition A.1])"

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MonoIncExtrap_Setting
import Definitions.Def_MonoIncExtrap_Algorithm1

open InnerProductSpace ThreeOpSplitting.Convergence

namespace MonoIncExtrap

/-- **`F + B` is maximal monotone.** arXiv:2206.00973v3, §1, p.2: "by the maximal monotonicity of
`B` and Assumptions 1(b) and 1(c), it can be observed that `F + B` is maximal monotone (e.g., see
[16, Proposition A.1])".

**Formalization Note.** `F` is constrained only on `cl(dom B)`; since `F + B` is empty off `dom B`,
values of `F` elsewhere do not matter. Maximality is among all operators on `ℝⁿ`. -/
theorem sum_maximal_monotone {n : ℕ} {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {B : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n))} {μ : ℝ}
    (h : Assumption1 F B μ) : IsMaximalMonotone (sumOp F B) := by sorry

end MonoIncExtrap
