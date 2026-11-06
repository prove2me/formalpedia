-- Prove2me | Theorems.Thm_NewtonLCP_theorem_6_4
-- name    : NewtonLCP.theorem_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:31:38.280799+00:00
-- url     : https://prove2.me/theorems/b9b31610-e175-4710-a8f0-e1da87fe7e78
-- title:
--   Theorem 6.4 — two Newton steps stay in $\mathcal N^R(\beta)$ with $\delta=\Theta(1/(n^{9/8}\sqrt{1+\kappa}))$
-- statement:
--   Let $M\in\mathcal P_\star(\kappa)$, $n\ge1$, and take
--
--   $$\beta\in\Big[\frac1{8192n^{3/2}},\frac1{4096n^{3/2}}\Big],\qquad\delta\in\Big[\frac1{2436n^{9/8}\sqrt{1+\kappa}},\frac1{1218n^{9/8}\sqrt{1+\kappa}}\Big].$$
--
--   Suppose $(x,s,\mu)\in\mathcal N^R(\beta)$ and set $\mu'=\mu/(1+\delta)$. Two successive Newton steps toward $\mu'$, as in (10), produce iterates $(x',s'),(x'',s'')\in\mathcal F_{>0}$ with
--
--   $$(x'',s'',\mu')\in\mathcal N^R(\beta).$$
--
--   This is the step that reduces $\mu$ by a constant factor in $O(n^{9/8}\sqrt{1+\kappa})$ Newton steps (second branch of (54)).
--
--   **Formalization Note** The first step is taken at $(x,s,\mu')$ and the second at $(x',s',\mu')$.
--
--   Differences from the source:
--   - encoding: n arbitrary → [Nonempty ι] (n ≥ 1); reason: the intervals for β and δ divide by n; the case n = 0 is undefined
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab…), Theorem 6.4, p.24 (proof §9.2, p.35)

import Mathlib
import Definitions.Def_NewtonLCP_Handicap
import Definitions.Def_NewtonLCP_InNR

namespace NewtonLCP

/-- **Theorem 6.4** (two Newton steps in the Rump neighbourhood). Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8), Theorem 6.4, p.24
(proof §9.2, p.35).

Let `M ∈ P⋆(κ)`, and set `β ∈ [1/(8192n^{3/2}), 1/(4096n^{3/2})]` and
`δ ∈ [1/(2436n^{9/8}√(1+κ)), 1/(1218n^{9/8}√(1+κ))]`. Suppose `(x, s, µ) ∈ N^R(β)`, and set
`µ' = µ/(1+δ)`. Two successive Newton steps toward `µ'`, as in (10), produce two iterates
`(x', s'), (x'', s'') ∈ F_{>0}` with `(x'', s'', µ') ∈ N^R(β)`.

**Formalization Note.** `n = Fintype.card ι ≥ 1` (`[Nonempty ι]`; the intervals divide by `n`).
The first step is the Newton step (10) at `(x, s, µ')`, the second at `(x', s', µ')`. -/
theorem theorem_6_4 {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (M : Matrix ι ι ℝ)
    (q : ι → ℝ) (κ β δ : ℝ) (x s : ι → ℝ) (mu : ℝ) (hM : IsPStarK M κ)
    (hβ : 1 / (8192 * (Fintype.card ι : ℝ) ^ ((3 : ℝ) / 2)) ≤ β ∧
      β ≤ 1 / (4096 * (Fintype.card ι : ℝ) ^ ((3 : ℝ) / 2)))
    (hδ : 1 / (2436 * (Fintype.card ι : ℝ) ^ ((9 : ℝ) / 8) * Real.sqrt (1 + κ)) ≤ δ ∧
      δ ≤ 1 / (1218 * (Fintype.card ι : ℝ) ^ ((9 : ℝ) / 8) * Real.sqrt (1 + κ)))
    (hNR : InNR M q β x s mu) :
    let mu' := mu / (1 + δ)
    let x' := x + newtonDx M x s mu'
    let s' := s + newtonDs M x s mu'
    let x'' := x' + newtonDx M x' s' mu'
    let s'' := s' + newtonDs M x' s' mu'
    (x', s') ∈ FeasPos M q ∧ (x'', s'') ∈ FeasPos M q ∧ InNR M q β x'' s'' mu' := by sorry

end NewtonLCP
