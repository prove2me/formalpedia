-- Prove2me | Theorems.Thm_LagrangeRank_Debias_Supplement_theorem_4_2
-- name    : LagrangeRank.Debias.Supplement.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:54:26.866122+00:00
-- url     : https://prove2.me/theorems/e6fc6471-934e-4711-9fcc-ba70d427f281
-- title:
--   Theorem 4.2 — BY FDR bound with the exact finite remainder
-- statement:
--   Fix dynamic range $\kappa\ge1$, regularization coefficient $c>0$, test level $0<\alpha<1$, and positive constants $c',c_3,K_D$. There are constants $C_0,C>0$, chosen before the problem and parameter sequences, such that the following holds. Suppose $n,L\to\infty$, $p\ge C_0\log n/n$ eventually, both Theorem 3.2 rate terms and both Theorem 3.3 rate terms tend to zero, and the centered true scores have dynamic range at most $\kappa$. Let every $R_i$ be an arbitrary ranking property in Definition 2.3.
--
--   Write $R_D(n,L,p,c')$ for the entire sufficient expression on p. 54 of Remark D.1, implemented by `remarkR` and displayed in MODERATION_NOTES.md. Require exactly the quantitative scaling condition
--   $$R_D(n,L,p,c')\le K_D\{L^{-c_3}+n^{-5}\}\quad\text{eventually}.$$
--   For the concrete p-values from the single-test perturbation boxes and the Benjamini–Yekutieli rule with $N=\sum_{k=1}^n1/k$, let $H_0$ be the set of true null hypotheses. Then, eventually,
--   $$\mathrm{FDR}\le\frac{|H_0|}{n}\alpha+C|H_0|\left(L^{-c_3}+\frac2{n^5}\right).$$
--   The coefficient 2 and the true-null fraction are retained. No independence of p-values, approximate superuniformity, or vanishing of $|H_0|(L^{-c_3}+2n^{-5})$ is assumed. This is the source's quantitative inequality, not just its asymptotic consequence.
--
--   Differences from the source:
--   - encoding: sample size n and repeated-comparison count L tend to infinity → a separate sequence index t, dimensions n(t), L(t), and finite product probability spaces; reason: the law at each problem size is exactly (2.1); both graph and comparison randomness remain
--   - reading: the finite remainder inequality in an asymptotic problem with c3 satisfying Remark D.1 → an eventual inequality with all terms of the Remark D.1 sufficient rate, fixed c′, c3 and KD; reason: the explicit sufficient expression on pp. 53–54 pins down the exponent rather than assuming the desired bootstrap error bound
--   - encoding: a p-value defined as an infimum of rejection levels → levels in (0,1), with value 1 if the set is empty; reason: p-values remain in [0,1]; no rejection at an empty infimum is introduced, and BY critical levels are strictly below 1
-- source:
--   Liu, Fang, Lu, Lagrangian Inference for Ranking Problems, arXiv:2110.00151v1, p. 27, Theorem 4.2

import Mathlib
import Definitions.Def_LagrangeRank_Debias_Supplement_Ranking

namespace LagrangeRank.Debias.Supplement

open MeasureTheory ProbabilityTheory Matrix Filter Topology
/-- The BY bound with its full quantitative remainder and Remark D.1 condition. -/
theorem theorem_4_2 (κ c cp c3 KD α : ℝ) (hκ : 1 ≤ κ) (hc : 0 < c)
    (hcp : 0 < cp) (hc3 : 0 < c3) (hKD : 0 < KD) (hα : 0 < α ∧ α < 1) :
    ∃ C0 C : ℝ, 0 < C0 ∧ 0 < C ∧
    ∀ (n L : ℕ → ℕ) (p : ℕ → unitInterval) (θ : (t : ℕ) → Vec (n t))
      (R : (t : ℕ) → Fin (n t) → Set (Ranking (n t))),
      Regime n L p → Density C0 n p → Rates32 n L p → Rates33 n L p →
      (∀ t, Parameter κ (θ t)) → (∀ t i, RankingProperty i (R t i)) →
      (∀ᶠ t in atTop, remarkR (n t) (L t) (p t) cp ≤
        KD * ((L t : ℝ)^(-c3) + (n t : ℝ)^(-5 : ℤ))) →
      ∀ᶠ t in atTop, fdr (L := L t) (p t) c α (θ t) (R t) ≤
        (nullCount (θ t) (R t) : ℝ) / n t * α +
        C * nullCount (θ t) (R t) * ((L t : ℝ)^(-c3) + 2 / (n t : ℝ)^5) := by sorry

end LagrangeRank.Debias.Supplement
