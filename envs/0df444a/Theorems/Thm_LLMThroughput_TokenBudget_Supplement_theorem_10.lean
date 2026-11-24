-- Prove2me | Theorems.Thm_LLMThroughput_TokenBudget_Supplement_theorem_10
-- name    : LLMThroughput.TokenBudget.Supplement.theorem_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:04:41.07956+00:00
-- url     : https://prove2.me/theorems/fdb1150e-d993-44d0-bc53-5d70444afc9e
-- title:
--   Theorem 10 (corrected: include the idle origin) — exact necessary-rate polygon
-- statement:
--   Let $a>0$ and $c\ge0$ be real costs, and let $b_0,b_{\max},k_{\max}$ be positive integers with $b_0\mid b_{\max}$ and $k_{\max}\le b_0$. Write $t_s=c+a\lceil s/b_0\rceil$ and define
--
--   $$O=(0,0),\quad A=\left(\frac{b_{\max}}{t_{b_{\max}}},0\right),\quad
--   B=\left(\frac{b_{\max}-k_{\max}+1}{t_{b_{\max}}},\frac{k_{\max}-1}{t_{b_{\max}}}\right),$$
--   $$C=\left(\frac{b_0-k_{\max}+1}{t_{b_0}},\frac{k_{\max}-1}{t_{b_0}}\right),\quad
--   D=\left(0,\frac{k_{\max}}{t_{k_{\max}}}\right).$$
--
--   For every nonnegative real rate pair $(\lambda_p,\lambda_d)$,
--
--   $$\operatorname{NecessaryCondition9}(\lambda_p,\lambda_d)\quad\Longleftrightarrow\quad
--   (\lambda_p,\lambda_d)\in\operatorname{conv}_{\mathbb R}\{O,A,B,C,D\}.$$
--
--   Here the left side is exactly the existence of a common nonnegative allocation of total mass at most one satisfying (33) and (34). This companion theorem characterizes the necessary relaxation, with both directions of the equivalence. It does not assert that every rate in the polygon is stabilizable. Coinciding vertices, $c=0$, $k_{\max}=1$ and $b_{\max}=b_0$ are included.
--
--   **Formalization Note** The polygon is the ordinary real convex hull in $\mathbb R\times\mathbb R$. All vertex subtractions and quotients are real. The idle origin repairs the printed statement: the zero allocation satisfies (33)–(34), whereas every convex combination of the four nonzero printed vertices has positive coordinate sum. The figure and proof explicitly use the origin.
--
--   Differences from the source:
--   - correction: convex hull of A,B,C,D → convex hull of O=(0,0),A,B,C,D with the four displayed vertices unchanged; reason: u=0 makes the origin feasible but the four-point hull excludes it; Figure 13 (p. 28) and Appendix E (p. 49) explicitly include O
--   - encoding: positive integer token, block and request budgets implicit in the batch model → explicit 0<b_0, 0<b_max and 0<k_max, with b_0 dividing b_max and k_max<=b_0; reason: these are the source budgets and ensure positive displayed denominators; c=0, k_max=1 and b_max=b_0 remain included
--   - encoding: an infinitely indexed nonnegative vector of total mass at most one in (33)–(34) → one common allocation on the finite contributing set M union {(0,k_max)}, with total mass at most one; reason: all coordinates outside this set have no contribution and may be zeroed in either direction
--   - encoding: empty batch has no token service → real 0/0 is assigned zero in the empty-batch terms; reason: this fixes the undefined empty-load display without removing c=0 or any rate pair
-- source:
--   Dai, Deng, Li & Peng, Throughput-Optimal Scheduling Algorithms for LLM Inference and AI Agents, arXiv:2504.07347v3, pp. 27–28, Theorem 10 and Figure 13; pp. 48–49, Appendix E

import Mathlib
import Definitions.Def_LLMThroughput_TokenBudget_Supplement_NecessaryCondition9

namespace LLMThroughput.TokenBudget.Supplement

/-- Theorem 10, correcting the omitted idle origin using Figure 13 and
Appendix E. This characterizes the necessary relaxation, not stability. -/
theorem theorem_10 (a c : ℝ) (b0 bmax kmax : ℕ)
    (ha : 0 < a) (hc : 0 ≤ c) (hb0 : 0 < b0) (hbmax : 0 < bmax)
    (hkmax : 0 < kmax) (hdiv : b0 ∣ bmax) (hk : kmax ≤ b0)
    (lambdaP lambdaD : ℝ) (hP : 0 ≤ lambdaP) (hD : 0 ≤ lambdaD) :
    NecessaryCondition9 a c b0 bmax kmax lambdaP lambdaD ↔
      (lambdaP, lambdaD) ∈ convexHull ℝ
        ({(0, 0),
          ((bmax : ℝ) / batchTime a c (b0 : ℝ) (bmax : ℝ), 0),
          (((bmax : ℝ) - (kmax : ℝ) + 1) /
              batchTime a c (b0 : ℝ) (bmax : ℝ),
            ((kmax : ℝ) - 1) / batchTime a c (b0 : ℝ) (bmax : ℝ)),
          (((b0 : ℝ) - (kmax : ℝ) + 1) /
              batchTime a c (b0 : ℝ) (b0 : ℝ),
            ((kmax : ℝ) - 1) / batchTime a c (b0 : ℝ) (b0 : ℝ)),
          (0, (kmax : ℝ) / batchTime a c (b0 : ℝ) (kmax : ℝ))} : Set (ℝ × ℝ)) := by sorry

end LLMThroughput.TokenBudget.Supplement
