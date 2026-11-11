-- Prove2me | Theorems.Thm_MeanCertificates1424_Hardness_theorem_1_1
-- name    : MeanCertificates1424.Hardness.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:52:26.852957+00:00
-- url     : https://prove2.me/theorems/ef820707-af90-4a83-8c10-c0a0caad8c34
-- title:
--   Theorem 1.1 — Optimal estimation factor and hardness of certification
-- statement:
--   For every fixed rational $0<\rho<1$, there is a deterministic polynomial-time construction which, on any finite simple graph $H$ with at least one edge and any integer $2\le k\le|V(H)|$, produces a feasible uniform-mean instance $I$ on $N$ vertices such that
--
--   $$\frac{N}{3k}\bigl(u(y)-\ell(y)\bigr)=\operatorname{dk}_k(H)+1.$$
--
--   The output graph is three-colorable and has diameter exactly two. There are no audits, $L=1$, $\epsilon=0$, reports lie in $\{0,1,2,3\}$, and the corruption budget satisfies $b\le\rho N$. Fields remain arbitrary real vectors subject only to the source's edge and common-mismatch constraints.
--
--   Under the operational Exponential Time Hypothesis, for every fixed real $\alpha\ge1$ no deterministic polynomial-time algorithm approximates the certificate width within factor $\alpha$. Moreover, for every fixed real $0<\delta\le1$, no deterministic polynomial-time estimator always achieves
--
--   $$\sup_{x\in C(y)}|a(y)-\mu(x)|\le(2-\delta)\,\frac{u(y)-\ell(y)}{2}.$$
--
--   Both hardness claims hold for every fixed rational $0<\rho<1$ under the same restrictions on graphs and reports. The construction is unconditional; ETH is used only for the two impossibility assertions. Algorithms may depend on fixed approximation parameters and the fixed corruption fraction, and must remain uniform over their input instances.
--
--   This is the complete headline theorem: it combines the exact reduction identity with both width-certification hardness and conditional-estimation hardness.
--
--   Differences from the source:
--   - encoding: finite graphs and rational binary numerical inputs, with real candidate fields → Fin n vertices, rational input data, real feasible vectors and EReal endpoint extrema; reason: finite labels and complete-lattice extrema preserve all instances in the complexity claim; every width promise is nonempty and anchored
--   - encoding: deterministic polynomial time and ETH on the number of SAT variables → finite Mathlib multi-stack machines, explicit binary adjacency-list codecs, uniform step bounds, normalized 3CNF and sublinear exponent ETH; reason: fixes an operational encoding without an optimum, real oracle, cost annotation, or correctness hypothesis on the program
--   - encoding: the construction and polynomial padding in the proof of Theorem 3.1 → the explicit indexed gadget and p=max(0,ceil(b/rho)-N0) middle-anchor padding; reason: chooses a concrete permitted labeling and padding amount; the output properties are conclusions
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Theorem 1.1, printed pp.1–2 (PDF pp.3–4)

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Computation

set_option autoImplicit false

namespace MeanCertificates1424.Hardness

/-- The complete Theorem 1.1, printed pp.1–2 / PDF pp.3–4.
The construction is unconditional. Only the two hardness assertions assume ETH.
ρ, α and δ are fixed before the programs and their uniform resource constants.
No width identity, feasibility proof, coloring or optimum is assumed as input. -/
theorem theorem_1_1 :
    (∀ ρ : ℚ, 0 < ρ → ρ < 1 →
      HeadlineConstructs ρ ∧
      ∀ (r : ℕ) (H : SimpleGraph (Fin r)) (k : ℕ), Admissible H k →
        let I := gadget H k (3 * k) (padding H k (3 * k) ρ)
        Restricted ρ I ∧
        (I.n : EReal) / (3 * k : ℝ) * width I = ((dks H k : ℝ) + 1 : ℝ)) ∧
    (ETH →
      (∀ (α : ℝ) (ρ : ℚ), 1 ≤ α → 0 < ρ → ρ < 1 → ¬ WidthAlgorithm α ρ) ∧
      (∀ (δ : ℝ) (ρ : ℚ), 0 < δ → δ ≤ 1 → 0 < ρ → ρ < 1 →
        ¬ Estimator (2 - δ) (Restricted ρ))) := by sorry

end MeanCertificates1424.Hardness
