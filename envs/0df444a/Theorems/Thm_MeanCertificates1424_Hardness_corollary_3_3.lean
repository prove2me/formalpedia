-- Prove2me | Theorems.Thm_MeanCertificates1424_Hardness_corollary_3_3
-- name    : MeanCertificates1424.Hardness.corollary_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:52:36.081549+00:00
-- url     : https://prove2.me/theorems/38e7d592-2c8e-4123-83ed-37975bcb1340
-- title:
--   Corollary 3.3 — The factor two is optimal
-- statement:
--   There exists a deterministic polynomial-time rational-output estimator attaining conditional error at most $2r(y)$ on every nonempty anchored uniform-mean instance with rational numerical inputs and no audits, where $r(y)=(u(y)-\ell(y))/2$. Assuming the operational Exponential Time Hypothesis, for every fixed real $0<\delta\le1$ and fixed rational $0<\rho<1$, no such machine always satisfies
--
--   $$\sup_{x\in C(y)}|a(y)-\mu(x)|\le(2-\delta)r(y).$$
--
--   The impossibility already holds on the restricted family with no audits, $L=1$, $\epsilon=0$, reports in $\{0,1,2,3\}$, three-colorable graphs of diameter exactly two, and $b\le\rho N$. It therefore also excludes an estimator with that guarantee on all nonempty anchored instances. The program and its polynomial resource constants may depend on fixed $\delta$ and $\rho$.
--
--   The unconditional positive existence claim is the uniform-mean comparison supplied by Proposition 5.6. Together with the conditional impossibility, it retains the source's final optimality sentence: factor two is the optimal polynomial-time constant under ETH.
--
--   Differences from the source:
--   - encoding: finite graphs and rational binary numerical inputs, with real candidate fields → Fin n vertices, rational input data, real feasible vectors and EReal endpoint extrema; reason: finite labels and complete-lattice extrema preserve all instances in the complexity claim; every width promise is nonempty and anchored
--   - encoding: deterministic polynomial time and ETH on the number of SAT variables → finite Mathlib multi-stack machines, explicit binary adjacency-list codecs, uniform step bounds, normalized 3CNF and sublinear exponent ETH; reason: fixes an operational encoding without an optimum, real oracle, cost annotation, or correctness hypothesis on the program
--   - encoding: the final sentence invokes the factor-two guarantee of Proposition 5.6 → an unconditional uniform-mean factor-two polynomial estimator is conjoined with the ETH-conditional impossibility; reason: spells out the positive half of the stated optimality comparison, with the full independent weighted/audited proposition outside this mission
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Corollary 3.3, printed p.8 (PDF p.10), proof continued printed p.9 (PDF p.11); positive uniform-mean comparison from Proposition 5.6, printed p.18 (PDF p.20)

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Computation

set_option autoImplicit false

namespace MeanCertificates1424.Hardness

/-- Corollary 3.3, printed p.8 / PDF p.10 (proof continues on PDF p.11).
The final optimality comparison includes the uniform-mean positive existence
claim supplied by Proposition 5.6, printed p.18 / PDF p.20. No endpoint oracle
is an input to either the positive or negative estimator predicate. -/
theorem corollary_3_3 :
    Estimator 2 Regular ∧
    (ETH → ∀ (δ : ℝ) (ρ : ℚ), 0 < δ → δ ≤ 1 → 0 < ρ → ρ < 1 →
      ¬ Estimator (2 - δ) (Restricted ρ)) := by sorry

end MeanCertificates1424.Hardness
