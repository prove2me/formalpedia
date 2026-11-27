-- Prove2me | Theorems.Thm_MPECRelax_ScholtesConv_Supplement_theorem_3_7
-- name    : MPECRelax.ScholtesConv.Supplement.theorem_3_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T11:33:02.584592+00:00
-- url     : https://prove2.me/theorems/533e0aee-2227-4da7-b1a4-615d0740d114
-- title:
--   Theorem 3.7, p. 17 — MPEC-LICQ implies GCQ for the Kadrani et al. relaxation R^KDB(t) near x*
-- statement:
--   Let $x^*$ be a feasible point of the MPEC (1), with continuously differentiable data, at which MPEC-LICQ holds. Then there are $\bar t>0$ and a neighborhood $N$ of $x^*$ such that, for every $t\in(0,\bar t)$ and every $\hat x\in N\cap X^{KDB}(t)$, the standard Guignard constraint qualification holds for $R^{KDB}(t)$ at $\hat x$:
--   $$T_{X^{KDB}(t)}(\hat x)^\circ=L_{X^{KDB}(t)}(\hat x)^\circ .$$
--   The neighborhood $N$ does not depend on $t$.
--
--   The result supports the existence of KKT multipliers for the relaxed programs used in Theorem 3.5. Example 3.6 shows that ACQ, and hence every stronger standard condition, can fail at such points, so GCQ is the natural level here.
--
--   **Formalization Note** Cones, GCQ and MPEC-LICQ are those of `MPECRelax.ScholtesConv.Supplement.CQ`; $X^{KDB}(t)$ is the feasible set of the NLP `RKDB P t`, with the constraints $g_i\le0$ and $h_j=0$ included.
--
--   Differences from the source:
--   - encoding: f, g_i, h_i, G_i, H_i are at least continuously differentiable (standing assumption, p. 1) → the hypothesis hP : P.IsC1 (every datum is ContDiff ℝ 1), so `gradient` is the true gradient; reason: the paper states the assumption once for the whole paper; it is carried explicitly, with the same instances
--   - encoding: ℝⁿ, indices i = 1, …, m (p, l), ∇g_i(x)ᵀd, a neighborhood N of x* → EuclideanSpace ℝ (Fin n), 0-based Fin indices, the inner product ⟪∇g_i(x), d⟫, N ∈ 𝓝 x*; reason: Lean conventions; same instances
-- source:
--   Hoheisel, Kanzow, Schwartz, Theoretical and numerical comparison of relaxation methods for mathematical programs with complementarity constraints, Preprint 299, Univ. Würzburg, Sept. 2010, p. 17, Theorem 3.7 (proof pp. 17–19)

import Mathlib
import Definitions.Def_MPECRelax_ScholtesConv_NLP
import Definitions.Def_MPECRelax_ScholtesConv_MPEC
import Definitions.Def_MPECRelax_ScholtesConv_Supplement_CQ
import Definitions.Def_MPECRelax_ScholtesConv_Supplement_KDB

open Filter Topology Set

namespace MPECRelax.ScholtesConv.Supplement

theorem theorem_3_7 {n m p l : ℕ} (P : MPEC n m p l) (hP : P.IsC1) (xs : E n)
    (hxs : P.Feasible xs) (hLICQ : MPEC_LICQ P xs) :
    ∃ tbar : ℝ, 0 < tbar ∧ ∃ N ∈ 𝓝 xs, ∀ t ∈ Ioo 0 tbar, ∀ x ∈ N,
      (RKDB P t).Feasible x → IsGCQ (RKDB P t) x := by sorry

end MPECRelax.ScholtesConv.Supplement
