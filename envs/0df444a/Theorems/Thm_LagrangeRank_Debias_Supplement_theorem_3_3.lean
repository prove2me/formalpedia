-- Prove2me | Theorems.Thm_LagrangeRank_Debias_Supplement_theorem_3_3
-- name    : LagrangeRank.Debias.Supplement.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:51:28.295749+00:00
-- url     : https://prove2.me/theorems/3505788a-522c-46f2-92f9-1a2633a5b97a
-- title:
--   Theorem 3.3 (corrected: density and nonzero inference contrasts) — uniform bootstrap calibration
-- statement:
--   For fixed bounded dynamic range $\kappa$ and positive regularization coefficient $c$, there is a sufficiently large density constant $C_0$ with the following property. Let $n,L\to\infty$, let $p\ge C_0\log n/n$ eventually, and suppose
--   $$\frac{n^2p\{\log(nL)\}^7}{L}\to0,\qquad \frac{n(\log n)^{3/2}}{\sqrt L}\to0.$$
--   For every deterministic nonempty inference pair set $E$ containing only distinct-item contrasts, the concrete statistic and conditional multiplier quantile (3.11)–(3.14) satisfy
--   $$\sup_{0<\alpha<1}\left|P\{T>c_W(\alpha,E)\}-\alpha\right|\longrightarrow0.$$
--   The realized comparison graph is sampled independently of the Bernoulli outcomes, and is separate from $E$. Every nonzero pair set and every test level in the open unit interval is retained. This is a corrected result: the printed unrestricted assertion is false, as documented by the diagonal and sparse witnesses in DISPROOF.md.
--
--   Differences from the source:
--   - correction: any E⊆V×V, including empty sets and zero contrasts → nonempty deterministic E with i≠j in every pair; reason: p. 49 (D.3) requires a positive contrast variance; a singleton diagonal gives T=W=cW=0 and calibration error 1, while adding a zero contrast can create an atom
--   - correction: only the two displayed rate conditions → also p≥C0 log n/n for sufficiently large fixed C0; reason: Appendix D, pp. 49–50 invokes the H.1 graph event; p=n^(−3), L=n^10 satisfies both printed rates but the graph is empty with probability tending to one; sparse disconnected sequences are excluded explicitly
--   - encoding: sample size n and repeated-comparison count L tend to infinity → a separate sequence index t, dimensions n(t), L(t), and finite product probability spaces; reason: the law at each problem size is exactly (2.1); both graph and comparison randomness remain
--   - encoding: inverse in (3.10) on the high-probability invertible graph event → the actual Matrix.inv, with zero on singular inputs; reason: under the stated sufficiently large graph-density constant the exceptional probability vanishes; no population inverse or CLIME estimate is substituted
-- source:
--   Liu, Fang, Lu, Lagrangian Inference for Ranking Problems, arXiv:2110.00151v1, p. 23, Theorem 3.3

import Mathlib
import Definitions.Def_LagrangeRank_Debias_Supplement_Bootstrap

namespace LagrangeRank.Debias.Supplement

open MeasureTheory ProbabilityTheory Matrix Filter Topology
/-- Corrected bootstrap theorem: graph density and nonzero contrasts are necessary, as D.3/H.1 show. -/
theorem theorem_3_3 (κ c : ℝ) (hκ : 1 ≤ κ) (hc : 0 < c) :
    ∃ C0 : ℝ, 0 < C0 ∧
    ∀ (n L : ℕ → ℕ) (p : ℕ → unitInterval) (θ : (t : ℕ) → Vec (n t))
      (E : (t : ℕ) → Finset (Fin (n t) × Fin (n t))),
      Regime n L p → Density C0 n p → Rates33 n L p →
      (∀ t, Parameter κ (θ t)) →
      (∀ t, (E t).Nonempty ∧ ∀ ij ∈ E t, ij.1 ≠ ij.2) →
      Tendsto (fun t => tailError (L := L t) (p t) c (θ t) (E t)) atTop (𝓝 0) := by sorry

end LagrangeRank.Debias.Supplement
