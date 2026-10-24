-- Prove2me | Theorems.Thm_OAI_PinchedHartogs_BaseConstruction_analytic_jet_bound
-- name    : OAI.PinchedHartogs.BaseConstruction.analytic_jet_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T16:03:51.40398+00:00
-- url     : https://prove2.me/theorems/8110e116-f263-4d1e-a86d-35e346d9c132
-- title:
--   Cauchy estimates for all derivatives of a bounded holomorphic map between complex normed spaces
-- statement:
--   The constant `cauchyJetConstant n` is from the definitions bundle of this split that holds only it: $C_0 = 1$ and $C_{n+1} = 4 \cdot 2^n\, C_n$, so $C_n = 4^n\, 2^{n(n-1)/2}$.
--
--   **Statement.** Let $E$ be a complex normed space and $F$ a complex Banach space (`CompleteSpace F`). Let $c \in E$, $0 \le r < R$ and $A \ge 0$, and let $f : E \to F$ be analytic at every point of the ball $B(c, R)$ (`AnalyticOnNhd ℂ f (Metric.ball c R)`) with $\|f(x)\| \le A$ for every $x \in B(c, R)$. Then for every $n \in \mathbb N$ and every $x \in B(c, r)$, the $n$-th Fréchet derivative (`iteratedFDeriv ℂ n f x`, an $n$-linear map with its operator norm) satisfies
--   $$\|D^n f(x)\| \;\le\; \frac{C_n\, A}{(R - r)^n}.$$
--
--   This is a form of Cauchy's estimates for holomorphic maps between Banach spaces (classical), with an explicit constant. The paper applies Cauchy estimates in Section 6 to bound the derivatives of the controlled base potential.
--
--   Lean: `OAI.PinchedHartogs.BaseConstruction.analytic_jet_bound`, OpenAI's theorem of that name (in `lean/OAI/Geometry/Kahler/BaseCauchyJets.lean`). The statement imports only Mathlib and the one-definition bundle with `cauchyJetConstant`. On this platform, `FamousTheorems.cauchy_estimate` (7a62ab17) is the first-derivative case for functions of one complex variable, and `LeblSCV.Holomorphic.cauchy_derivative_formula_and_estimates` gives the coefficient estimates on polydiscs in $\mathbb C^n$; neither covers all derivatives of maps between normed spaces.
-- source:
--   classical (Cauchy's estimates, in the form for holomorphic maps between Banach spaces); proof and Lean code: OpenAI, A negatively pinched Kähler threefold without bounded holomorphic coordinates, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 359; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-negatively-pinched-Kahler-threefold-without-bounded-holomorphic-coordinates-September-25-2026/paper.pdf, Section 6; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Kahler/BaseCauchyJets.lean (declaration OAI.PinchedHartogs.BaseConstruction.analytic_jet_bound)

import Mathlib
import Definitions.Def_OAIQWPH000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler8342_1 uKahler8342_2 uKahler8392_1 uKahler8392_2

open scoped ContDiff
open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open Set Filter Topology MeasureTheory
open scoped ContDiff ComplexOrder
noncomputable section

open Set Filter Topology
namespace PinchedHartogs.BaseConstruction

lemma analytic_jet_bound {E : Type uKahler8342_1} {F : Type uKahler8342_2} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : E → F} {c : E} {R r A : ℝ} (hRr : r < R) (hr : 0 ≤ r) (hA : 0 ≤ A)
    (hf : AnalyticOnNhd ℂ f (Metric.ball c R))
    (hb : ∀ x ∈ Metric.ball c R, ‖f x‖ ≤ A) (n : ℕ) :
    ∀ x ∈ Metric.ball c r, ‖iteratedFDeriv ℂ n f x‖ ≤ cauchyJetConstant n*A/(R-r)^n := by
  sorry

end PinchedHartogs.BaseConstruction

end

end OAI
end
