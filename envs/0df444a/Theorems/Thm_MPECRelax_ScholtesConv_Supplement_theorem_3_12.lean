-- Prove2me | Theorems.Thm_MPECRelax_ScholtesConv_Supplement_theorem_3_12
-- name    : MPECRelax.ScholtesConv.Supplement.theorem_3_12
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T11:34:47.035022+00:00
-- url     : https://prove2.me/theorems/6aecbab5-2d5e-47c4-9d03-0637b481ee3e
-- title:
--   Theorem 3.12, p. 23 — MPEC-LICQ implies LICQ for R^SU(t) wherever I_Φ(x, t) ∩ (I_G(x) ∪ I_H(x)) = ∅
-- statement:
--   Let $\theta$ satisfy conditions (a)–(e) of p. 20–21 and let $R^{SU}(t)$ be the corresponding local relaxation. Let $x^*$ be a feasible point of the MPEC (1), with continuously differentiable data, at which MPEC-LICQ holds. Then there is a neighborhood $N$ of $x^*$ such that, for every $t>0$, every $x\in N\cap X^{SU}(t)$ with
--   $$I_\Phi(x,t)\cap\bigl(I_G(x)\cup I_H(x)\bigr)=\emptyset$$
--   satisfies standard LICQ for $R^{SU}(t)$.
--
--   Thus the relaxation satisfies the strongest standard constraint qualification wherever the smoothing part of the constraint $\Phi^{SU}\le0$ is active away from the axes.
--
--   **Formalization Note** The statement puts no restriction on $t$ other than $t>0$, under which $R^{SU}(t)$ and its index sets are defined (p. 22); so $N$ is chosen once, before $t$, and the conclusion is claimed for every $t>0$.
--
--   Differences from the source:
--   - encoding: f, g_i, h_i, G_i, H_i are at least continuously differentiable (standing assumption, p. 1) → the hypothesis hP : P.IsC1 (every datum is ContDiff ℝ 1), so `gradient` is the true gradient; reason: the paper states the assumption once for the whole paper; it is carried explicitly, with the same instances
--   - encoding: ℝⁿ, indices i = 1, …, m (p, l), ∇g_i(x)ᵀd, a neighborhood N of x* → EuclideanSpace ℝ (Fin n), 0-based Fin indices, the inner product ⟪∇g_i(x), d⟫, N ∈ 𝓝 x*; reason: Lean conventions; same instances
--   - encoding: θ : [−1, 1] → ℝ satisfying (a)–(e) (pp. 20–21) → θ : ℝ → ℝ with IsSUTheta θ: C² on [−1, 1], with θ′, θ″ at ±1 taken within [−1, 1] (one-sided); θ is a parameter and the theorem holds for every admissible θ; reason: ϕ(·; t) only evaluates θ on (−1, 1), so values off [−1, 1] change no instance; one-sided derivatives are what the conditions at the endpoints of [−1, 1] mean
--   - reading: no range on t is stated; the index sets are defined for "t > 0 and x̂ ∈ X^SU(t)" (p. 22), and the page writes I_Φ(x, t) with Φ for Φ^SU → ∃ N ∈ 𝓝 x*, ∀ t > 0, ∀ x ∈ N ∩ X^SU(t), …, with I_Φ = IPhiSU; reason: t > 0 is the domain on which R^SU(t) is defined; the literal statement chooses N independently of t, and no t̄ is added
-- source:
--   Hoheisel, Kanzow, Schwartz, Theoretical and numerical comparison of relaxation methods for mathematical programs with complementarity constraints, Preprint 299, Univ. Würzburg, Sept. 2010, p. 23, Theorem 3.12 (proof pp. 23–24); index sets p. 22

import Mathlib
import Definitions.Def_MPECRelax_ScholtesConv_NLP
import Definitions.Def_MPECRelax_ScholtesConv_MPEC
import Definitions.Def_MPECRelax_ScholtesConv_Supplement_CQ
import Definitions.Def_MPECRelax_ScholtesConv_Scholtes
import Definitions.Def_MPECRelax_ScholtesConv_Supplement_SU

open Filter Topology Set

namespace MPECRelax.ScholtesConv.Supplement

theorem theorem_3_12 {n m p l : ℕ} (P : MPEC n m p l) (hP : P.IsC1)
    (θ : ℝ → ℝ) (hθ : IsSUTheta θ) (xs : E n)
    (hxs : P.Feasible xs) (hLICQ : MPEC_LICQ P xs) :
    ∃ N ∈ 𝓝 xs, ∀ t : ℝ, 0 < t → ∀ x ∈ N, (RSU P θ t).Feasible x →
      IPhiSU P θ x t ∩ (P.IG x ∪ P.IH x) = ∅ → IsLICQ (RSU P θ t) x := by sorry

end MPECRelax.ScholtesConv.Supplement
