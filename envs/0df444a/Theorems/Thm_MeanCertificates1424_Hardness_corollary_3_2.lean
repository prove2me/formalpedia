-- Prove2me | Theorems.Thm_MeanCertificates1424_Hardness_corollary_3_2
-- name    : MeanCertificates1424.Hardness.corollary_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:52:16.234867+00:00
-- url     : https://prove2.me/theorems/c26fac5a-c624-43cd-a6b7-4dda6421677b
-- title:
--   Corollary 3.2 — No constant-factor approximation without audits
-- statement:
--   Assume the operational Exponential Time Hypothesis. For every fixed real $\alpha\ge1$ and fixed rational $0<\rho<1$, there is no deterministic polynomial-time machine which, on every feasible uniform-mean instance in the restricted family, returns a rational $a$ with
--
--   $$\frac{u(y)-\ell(y)}{\alpha}\le a\le\alpha\bigl(u(y)-\ell(y)\bigr).$$
--
--   The family has no audits, $L=1$, noiseless reports in $\{0,1,2,3\}$, three-colorable graphs of diameter exactly two, and $b\le\rho N$. Algorithms may depend on the fixed approximation factor and corruption fraction, but must be uniform over all input instances.
--
--   The conclusion rules out any constant-factor certificate of the remaining aggregate uncertainty, even within this restricted family. The external densest-subgraph hardness implication is part of the proof obligation and is not assumed as a separate hypothesis.
--
--   Differences from the source:
--   - encoding: finite graphs and rational binary numerical inputs, with real candidate fields → Fin n vertices, rational input data, real feasible vectors and EReal endpoint extrema; reason: finite labels and complete-lattice extrema preserve all instances in the complexity claim; every width promise is nonempty and anchored
--   - encoding: deterministic polynomial time and ETH on the number of SAT variables → finite Mathlib multi-stack machines, explicit binary adjacency-list codecs, uniform step bounds, normalized 3CNF and sublinear exponent ETH; reason: fixes an operational encoding without an optimum, real oracle, cost annotation, or correctness hypothesis on the program
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Corollary 3.2, printed p.8 (PDF p.10)

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Computation

set_option autoImplicit false

namespace MeanCertificates1424.Hardness

/-- Corollary 3.2, printed p.8 / PDF p.10. The ordinary operational ETH is the
only complexity hypothesis; Manurangsi's implication is proof work, not a premise.
Programs may depend on fixed α and ρ, never on the particular input. -/
theorem corollary_3_2 :
    ETH → ∀ (α : ℝ) (ρ : ℚ), 1 ≤ α → 0 < ρ → ρ < 1 →
      ¬ WidthAlgorithm α ρ := by sorry

end MeanCertificates1424.Hardness
