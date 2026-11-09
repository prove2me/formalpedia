-- Prove2me | Theorems.Thm_OracleStateHSP_fact_4_5
-- name    : OracleStateHSP.fact_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:31:33.884835+00:00
-- url     : https://prove2.me/theorems/eabee273-1433-47fa-9d7e-7ca3e7fcf901
-- title:
--   Fact 4.5 (Rescaling the oracle, [Bel15, Proposition 6(d)])
-- statement:
--   For every matrix $A$ indexed by a finite set $X$, every family $\Delta = (\Delta_{xy})$ of matrices on a finite-dimensional register and every nonzero scalar $c \in \mathbb C$,
--   $$
--   \gamma_2(A \mid c\,\Delta) = \frac{1}{|c|}\, \gamma_2(A \mid \Delta).
--   $$
--
--   Reducing the oracle differences by a factor $c$ scales the adversary bound by $1/|c|$; with $c = \sqrt\varepsilon$ this produces the $\varepsilon$-dependence of the lower bound. The paper cites it from Belovs (Proposition 6(d)).
--
--   **Formalization Note** Both sides lie in $[0, \infty]$; an infeasible program stays infeasible ($\infty / |c| = \infty$).
--
--   Differences from the source:
--   - reading: the relative γ2 norm (not defined in the paper) → Belovs's definition, as in Theorem 4.4; reason: the paper cites Belovs for the norm
--   - encoding: real values → values in ℝ≥0∞ with division by ENNReal.ofReal |c|; reason: the norm may be ∞ when the program is infeasible
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, Fact 4.5, p.36 (cited: [Bel15, Proposition 6(d)])

import Mathlib
import Definitions.Def_OracleStateHSP_relGamma2
open scoped ENNReal

namespace OracleStateHSP

/-- Fact 4.5 of Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, p.36 (rescaling the oracle, cited there from A. Belovs, *Variations on
quantum adversary*, arXiv:1504.06943, Proposition 6(d)): for every nonzero scalar `c`,
`γ₂(A | c Δ) = (1/|c|) γ₂(A | Δ)`.

**Formalization Note.** Values in `ℝ≥0∞` (`⊤ / |c| = ⊤`, consistent with an infeasible program
staying infeasible). -/
theorem fact_4_5 {X Q : Type*} [Fintype X] [Fintype Q] (A : Matrix X X ℂ)
    (Δ : X → X → Matrix Q Q ℂ) (c : ℂ) (hc : c ≠ 0) :
    relGamma2 A (fun x y => c • Δ x y) = relGamma2 A Δ / ENNReal.ofReal ‖c‖ := by sorry

end OracleStateHSP
