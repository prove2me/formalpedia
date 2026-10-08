-- Prove2me | Theorems.Thm_KhachiyanRound_BCD_theorem_2
-- name    : KhachiyanRound.BCD.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:16:07.851981+00:00
-- url     : https://prove2.me/theorems/7f6dbf75-0511-43bc-8eae-5912c7e52f3c
-- title:
--   Theorem 2, p. 317 — the BCD computes a (1 + ε)n-rounding ellipsoid of m points in ℝⁿ within O(n(1/ε + ln n + ln ln m)) iterations
-- statement:
--   There is a universal constant $C > 0$ with the following property. Let $n \ge 1$, let $\mathcal A = \{a_1,\dots,a_m\} \subset \mathbb{R}^n$ have affine hull $\mathbb{R}^n$, and let $\varepsilon > 0$. Run the BCD method on the centrally symmetric lifted set $\mathcal A' = \{\pm(a_j;1)\} \subset \mathbb{R}^{n+1}$ of (3.3) — with any tie-breaking rule — producing iterates $p_0, p_1, \dots$, and let $p_j = p_j^+ + p_j^-$ denote aggregated weights. Then there is an iterate $p_k$ with
--   $$k \le C\,(n+1)\Big(\frac1\varepsilon + \ln(n+1) + \ln\ln(2m)\Big)$$
--   that satisfies the relaxed optimality conditions (2.10) on $\mathcal A'$ with $\varepsilon' = \frac{n}{n+1}\varepsilon$ (3.2), whose moment matrix is positive definite, and for which the ellipsoid
--   $$E = \big\{x \in \mathbb{R}^n \;\big|\; (x;1) \in \sqrt{1+(1+\varepsilon)n}\;E'_{p_k}\big\}$$
--   of Lemma 5 is a $(1+\varepsilon)n$-rounding of $\mathcal A$ (1.2):
--   $$[(1+\varepsilon)n]^{-1}E \subseteq \operatorname{conv}(\mathcal A) \subseteq E,$$
--   the shrinking being about the centre $b = \sum_j p_j a_j$ of $E$.
--
--   This is the paper's main result: a simple first-order method computes a near-optimal rounding ellipsoid of an arbitrary polytope given by its vertices, in a number of iterations that depends on $m$ only through $\ln\ln m$.
--
--   **Formalization Note** The page states $N(\varepsilon) = O(mn^2(\varepsilon^{-1} + \ln n + \ln\ln m))$ arithmetic operations and comparisons. The Lean statement bounds the index of an iterate that passes the stopping test; the cost per iteration ($O(nm)$, from the rank-one correction) and the $O(mn^2)$ cost of forming $A_0^{-1}$ are not formalized. The bound is written in the lifted parameters $(n+1, 2m)$, which keeps it positive for every $n\ge1$ (at $n = 1$, $m = 2$ the page's $\ln n + \ln\ln m$ is negative); wherever the page's expression is meaningful the two agree up to the constant. The constant $C$ is quantified before every instance datum. $E'_{p}$ is the ellipsoid (3.4) of the aggregated weights.
-- source:
--   Khachiyan, Rounding of polytopes in the real number model of computation, Math. Oper. Res. 21 (1996), p. 317, Theorem 2; (1.2), p. 307; (3.2)–(3.4), p. 315

import Mathlib
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_KhachiyanRound_BCD_Setting

open scoped Pointwise

namespace KhachiyanRound.BCD

theorem theorem_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ) (a : Fin m → Fin n → ℝ), 1 ≤ n →
      affineSpan ℝ (Set.range a) = ⊤ → ∀ ε : ℝ, 0 < ε →
        ∀ p : ℕ → (Fin m ⊕ Fin m → ℝ), IsBCDRun (liftPts a) p →
          ∃ k : ℕ, (k : ℝ) ≤ C * (n + 1) *
              (1 / ε + Real.log (n + 1) + Real.log (Real.log (2 * m))) ∧
            IsRelaxedOpt (liftPts a) (p k) ((n : ℝ) / (n + 1) * ε) ∧
            (momentMatrix (liftPts a) (p k)).PosDef ∧
            (AffineMap.homothety (∑ j, aggr (p k) j • a j) ((1 + ε) * (n : ℝ))⁻¹) ''
                lemma5Ellipsoid a (aggr (p k)) ε ⊆ convexHull ℝ (Set.range a) ∧
            convexHull ℝ (Set.range a) ⊆ lemma5Ellipsoid a (aggr (p k)) ε := by sorry
end KhachiyanRound.BCD
