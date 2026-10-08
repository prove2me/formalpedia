-- Prove2me | Theorems.Thm_NagaevLD_GenMoment_per_factor_bound
-- name    : NagaevLD.GenMoment.per_factor_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:17:32.281511+00:00
-- url     : https://prove2.me/theorems/58e8a061-5774-4849-9ea5-66267d3e21a4
-- title:
--   Proof of Theorem 2.5, p. 768 — Ee^{hX_j} ≤ (b_j(x/n) + b_gj)exp{hx/n − g(x/n)}, h = g′(x/n)
-- statement:
--   Let $X_j$ be a real random variable, let $g:\mathbb R\to\mathbb R$ have, on $[0,\infty)$, a positive nondecreasing derivative $g'$, and suppose
--   $$b_{gj}=E\big[e^{g(X_j)};X_j\ge 0\big]<\infty .$$
--   Let $n\ge 1$ be an integer, $x>0$, $h=g'(x/n)$, and $b_j(x/n)=e^{g(0)}E\big[e^{hX_j};X_j<0\big]$. Then
--   $$Ee^{hX_j}\ \le\ \big(b_j(x/n)+b_{gj}\big)\exp\{hx/n-g(x/n)\}.$$
--
--   This is the bound on each factor of the product in (2.45); multiplying these bounds over $j$ and inserting them in (2.45) with $h=g'(x/n)$ gives Theorem 2.5.
--
--   **Formalization Note** The finiteness of $b_{gj}$ is an explicit integrability hypothesis (Lean's integral of a non-integrable function is $0$). Under it $Ee^{hX_j}$ is finite. The hypotheses on $g$ are imposed on $[0,\infty)$ only, and $b_{gj}$ is the integral over $u\ge 0$ (see the definition file). The implicit $n\ge1$ of the paper is explicit in Lean.
-- source:
--   Nagaev, Large deviations of sums of independent random variables, Ann. Probab. 7 (1979), p. 768, proof of Theorem 2.5, after (2.48)

import Mathlib
import Definitions.Def_NagaevLD_GenMoment_Setting

open MeasureTheory ProbabilityTheory

namespace NagaevLD.GenMoment

/-- Proof of Theorem 2.5, p. 768, after (2.48): for `h = g′(x/n)`,
`E e^{hX_j} ≤ (b_j(x/n) + b_gj) exp{hx/n − g(x/n)}`. -/
theorem per_factor_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 0 < n) (X : Fin n → Ω → ℝ) (hXm : ∀ j, Measurable (X j))
    (g g' : ℝ → ℝ) (hg : ∀ u : ℝ, 0 ≤ u → HasDerivAt g (g' u) u)
    (hg'pos : ∀ u : ℝ, 0 ≤ u → 0 < g' u) (hg'mono : MonotoneOn g' (Set.Ici 0)) (j : Fin n)
    (hbg : IntegrableOn (fun ω => Real.exp (g (X j ω))) {ω | 0 ≤ X j ω} P)
    (x : ℝ) (hx : 0 < x) (h : ℝ) (hh : h = g' (x / n)) :
    ∫ ω, Real.exp (h * X j ω) ∂P
      ≤ (bj P X g g' j (x / n) + bg P X g j) * Real.exp (h * (x / n) - g (x / n)) := by sorry

end NagaevLD.GenMoment
