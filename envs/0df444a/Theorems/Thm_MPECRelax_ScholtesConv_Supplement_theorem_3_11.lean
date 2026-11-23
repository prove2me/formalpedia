-- Prove2me | Theorems.Thm_MPECRelax_ScholtesConv_Supplement_theorem_3_11
-- name    : MPECRelax.ScholtesConv.Supplement.theorem_3_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:34:15.999103+00:00
-- url     : https://prove2.me/theorems/0f51b64c-1d0a-426f-abcf-67a38643d88f
-- title:
--   Theorem 3.11, p. 22 — MPEC-LICQ implies ACQ for the Steffensen–Ulbrich relaxation R^SU(t) near x*
-- statement:
--   Let $\theta$ satisfy conditions (a)–(e) of p. 20–21 and let $R^{SU}(t)$ be the corresponding local relaxation. Let $x^*$ be a feasible point of the MPEC (1), with continuously differentiable data, at which MPEC-LICQ holds. Then there are a neighborhood $N$ of $x^*$ and $\bar t>0$ such that, for all $t\in(0,\bar t)$ and all $\hat x\in X^{SU}(t)\cap N$, the standard Abadie constraint qualification holds for $R^{SU}(t)$ at $\hat x$:
--   $$T_{X^{SU}(t)}(\hat x)=L_{X^{SU}(t)}(\hat x).$$
--
--   Example 3.10 shows that CPLD can fail at such points, so ACQ is the level the relaxation keeps under MPEC-LICQ.
--
--   **Formalization Note** The theorem holds for every admissible $\theta$; $N$ and $\bar t$ may depend on $\theta$ (which is fixed with the program) but not on $t$.
--
--   Differences from the source:
--   - encoding: f, g_i, h_i, G_i, H_i are at least continuously differentiable (standing assumption, p. 1) → the hypothesis hP : P.IsC1 (every datum is ContDiff ℝ 1), so `gradient` is the true gradient; reason: the paper states the assumption once for the whole paper; it is carried explicitly, with the same instances
--   - encoding: ℝⁿ, indices i = 1, …, m (p, l), ∇g_i(x)ᵀd, a neighborhood N of x* → EuclideanSpace ℝ (Fin n), 0-based Fin indices, the inner product ⟪∇g_i(x), d⟫, N ∈ 𝓝 x*; reason: Lean conventions; same instances
--   - encoding: θ : [−1, 1] → ℝ satisfying (a)–(e) (pp. 20–21) → θ : ℝ → ℝ with IsSUTheta θ: C² on [−1, 1], with θ′, θ″ at ±1 taken within [−1, 1] (one-sided); θ is a parameter and the theorem holds for every admissible θ; reason: ϕ(·; t) only evaluates θ on (−1, 1), so values off [−1, 1] change no instance; one-sided derivatives are what the conditions at the endpoints of [−1, 1] mean
-- source:
--   Hoheisel, Kanzow, Schwartz, Theoretical and numerical comparison of relaxation methods for mathematical programs with complementarity constraints, Preprint 299, Univ. Würzburg, Sept. 2010, p. 22, Theorem 3.11 (proof pp. 22–23); θ, ϕ, Φ^SU pp. 20–21

import Mathlib
import Definitions.Def_MPECRelax_ScholtesConv_NLP
import Definitions.Def_MPECRelax_ScholtesConv_MPEC
import Definitions.Def_MPECRelax_ScholtesConv_Supplement_CQ
import Definitions.Def_MPECRelax_ScholtesConv_Supplement_SU

open Filter Topology Set

namespace MPECRelax.ScholtesConv.Supplement

theorem theorem_3_11 {n m p l : ℕ} (P : MPEC n m p l) (hP : P.IsC1)
    (θ : ℝ → ℝ) (hθ : IsSUTheta θ) (xs : E n)
    (hxs : P.Feasible xs) (hLICQ : MPEC_LICQ P xs) :
    ∃ N ∈ 𝓝 xs, ∃ tbar : ℝ, 0 < tbar ∧ ∀ t ∈ Ioo 0 tbar, ∀ x ∈ N,
      (RSU P θ t).Feasible x → IsACQ (RSU P θ t) x := by sorry

end MPECRelax.ScholtesConv.Supplement
