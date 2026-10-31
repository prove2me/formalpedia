-- Prove2me | Theorems.Thm_KallMayerSLP_Multistage_example_3_1
-- name    : KallMayerSLP.Multistage.example_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:20:47.20714+00:00
-- url     : https://prove2.me/theorems/aa6f1b7d-2d7f-4268-98a0-c2f4d44219a6
-- title:
--   Example 3.1 — without independence the discretization need not give a lower bound
-- statement:
--   Fix $\varepsilon\in(-1,1)$ and consider the three-stage complete fixed recourse problem
--   $$
--   V^*:=\min\{2x+\mathbb E[y_1(\xi_2)+2y_2(\xi_2)]+\mathbb E[z_1(\xi_2,\xi_3)+z_2(\xi_2,\xi_3)]\}
--   $$
--   subject to $x+y_1(\xi_2)-y_2(\xi_2)=\xi_2$, $x+y_1(\xi_2)-y_2(\xi_2)+z_1(\xi_2,\xi_3)-z_2(\xi_2,\xi_3)=\xi_3$, $x,y_1,y_2,z_1,z_2\ge0$, where $(\xi_2,\xi_3)$ has the density $f$ on $[0,1]^2$ equal to $1+\varepsilon$ on $[0,\tfrac12]^2\cup[\tfrac12,1]^2$ and $1-\varepsilon$ on the two other squares. Discretize by the trivial partition of $\Xi^2=[0,1]$ and the partition $\{[0,\tfrac12),[\tfrac12,1]\}$ of $\Xi^3=[0,1]$, and let $\bar V$ be the optimal value of the discretized problem. Then
--   $$
--   V^*=\frac{5-\varepsilon}{6},\qquad\bar V=\frac34,
--   $$
--   so $\bar V\le V^*$ if $\varepsilon\le\tfrac12$ and $\bar V>V^*$ if $\varepsilon>\tfrac12$.
--
--   For $\varepsilon\ne0$ the variables $\xi_2,\xi_3$ are dependent. So with dependent stages, even with randomness in the right-hand sides only and complete fixed recourse, discretization need not give a lower bound; this is why Assumption 3.2 asks for independence.
--
--   **Formalization Note** $\Omega=\mathbb R^2$ carries the law of $(\xi_2,\xi_3)$, and the discretized problem is the problem (3.14) of the tree `ex31Tree`, whose means and probabilities are the book's $\bar\xi_2=\tfrac12$, $\bar\xi_{31}=\tfrac14$, $\bar\xi_{32}=\tfrac34$, $p_{31}=p_{32}=\tfrac12$.
--
--   Differences from the source:
--   - encoding: ξ_2, ξ_3 real random variables and partitions of Ξ² × Ξ³ → ξ_t vectors of ℝ¹ on Ω = ℝ², and a scenario tree with cells in ℝ¹; reason: the same random variables and the same cells; the conditional means agree because ξ_2 is not subdivided
--   - encoding: min → infimum in EReal; reason: +∞ on infeasible and -∞ on unbounded problems; the book assumes neither case away
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, Example 3.1, pp.257–260 (PDF 266–269)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_value
import Definitions.Def_KallMayerSLP_Multistage_aggValue
import Definitions.Def_KallMayerSLP_Multistage_ex31Measure
import Definitions.Def_KallMayerSLP_Multistage_ex31Xi
import Definitions.Def_KallMayerSLP_Multistage_ex31Tree

namespace KallMayerSLP.Multistage

open MeasureTheory

/-- **Chapter 3, Example 3.1** (Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3,
Example 3.1, pp.257–260, PDF 266–269): for `ε ∈ (-1, 1)`, the three-stage complete fixed recourse
problem with dependent `ξ_2`, `ξ_3` has optimal value `V* = (5 − ε)/6`, its discretization has
optimal value `V̄ = 3/4`, and `V̄ ≤ V*` if `ε ≤ 1/2`, `V̄ > V*` if `ε > 1/2`. So without the
stochastic independence of Assumption 3.2 the aggregated problem need not give a lower bound.

**Formalization Note.** `Ω = ℝ²` with the law of `(ξ_2, ξ_3)`, and the discretization is the tree
`ex31Tree`. Here the marginals of `ξ_2` and `ξ_3` are uniform on `[0, 1]`, and `Ξ^2` is not
subdivided, so the means and probabilities of (3.13) are the book's `ξ̄_2 = 1/2`, `ξ̄_31 = 1/4`,
`ξ̄_32 = 3/4` and `p_31 = p_32 = 1/2` (p.259, PDF 268). -/
theorem example_3_1 {ε : ℝ} (hε₁ : -1 < ε) (hε₂ : ε < 1) :
    value ex31Data (ex31Measure ε) ex31Xi = (((5 - ε) / 6 : ℝ) : EReal) ∧
      aggValue ex31Tree (ex31Measure ε) ex31Xi = ((3 / 4 : ℝ) : EReal) ∧
      (ε ≤ 1 / 2 → aggValue ex31Tree (ex31Measure ε) ex31Xi ≤ value ex31Data (ex31Measure ε) ex31Xi) ∧
      (1 / 2 < ε →
        value ex31Data (ex31Measure ε) ex31Xi < aggValue ex31Tree (ex31Measure ε) ex31Xi) := by sorry

end KallMayerSLP.Multistage
