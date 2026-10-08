-- Prove2me | Theorems.Thm_FunctionalIto_Formula_theorem_4_1
-- name    : FunctionalIto.Formula.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:11:25.903534+00:00
-- url     : https://prove2.me/theorems/a313a970-0a10-43ac-9cbd-bd1990f68572
-- title:
--   Theorem 4.1, p. 11 — functional Itô formula (30) for F ∈ ℂ_b^{1,2} verifying (10)
-- statement:
--   Let $X$ be a continuous $\mathbb R^d$-valued semimartingale on a filtered probability space satisfying the usual hypotheses, with quadratic covariation $[X](t)=\int_0^tA(s)\,ds$ for a cadlag process $A$ with values in the positive semidefinite matrices. Let $F$ be a nonanticipative functional in $\mathbb C^{1,2}_b([0,T))$, with horizontal derivative $\mathcal DF$, vertical derivative $\nabla_xF$ and second vertical derivative $\nabla_x^2F$, which verifies the predictable-dependence condition (10): $F_t(x_t,v_t)=F_t(x_t,v_{t-})$. Then for every $t\in[0,T)$, almost surely,
--   $$F_t(X_t,A_t)-F_0(X_0,A_0)=\int_0^t\mathcal D_uF(X_u,A_u)\,du+\int_0^t\nabla_xF_u(X_u,A_u)\cdot dX(u)+\int_0^t\tfrac12\operatorname{tr}\big(\nabla_x^2F_u(X_u,A_u)\,d[X](u)\big).$$
--
--   The process $Y(t)=F_t(X_t,A_t)$ is thus reconstructed from the second-order jet $(\mathcal DF,\nabla_xF,\nabla_x^2F)$ of $F$ along the paths of $X$. For $F_t(x,v)=f(t,x(t))$ the formula is the classical Itô formula; it also covers functionals of the whole path and of the quadratic variation, such as $\int_0^tg(x(u))v(u)\,du$ or $e^{x(t)-\frac12\int_0^tv(u)du}$.
--
--   **Formalization Note.** The Itô integral $\int_0^t\nabla_xF_u(X_u,A_u)\cdot dX(u)$ is the limit in probability of the dyadic left Riemann sums $\sum_{k<2^n}\nabla_xF_{t_k}(X_{t_k},A_{t_k})\cdot(X(t_{k+1})-X(t_k))$, $t_k=kt/2^n$ (the published `EthierKurtz.itoStepSum`, summed over the coordinates). The theorem is stated as: these sums converge in probability to $F_t(X_t,A_t)-F_0(X_0,A_0)-\int_0^t\mathcal D_uF\,du-\frac12\int_0^t\operatorname{tr}(\nabla_x^2F_u\,A(u))\,du$. Since limits in probability are almost surely unique, this is the almost-sure identity (30). For this integrand the left Riemann sums do converge to the Itô integral: by left-continuity of $\nabla_xF$ the step integrands converge pointwise to $\nabla_xF_u(X_u,A_{u-})$, which differs from $\nabla_xF_u(X_u,A_u)$ only at the countably many jump times of $A$, a null set for $dX$, and the derivatives are locally bounded ($\mathbb B$), so the dominated convergence theorem for stochastic integrals applies. $d[X](u)=A(u)\,du$ by (3), and $\operatorname{tr}(\nabla_x^2F\,A)=\sum_{i,j}(\nabla_x^2F)_{ij}A_{ji}$. All processes are indexed by $[0,\infty)$; only $[0,T]$ matters.
-- source:
--   Cont and Fournié, Functional Itô calculus and stochastic integral representation of martingales, arXiv:1002.2446v5, p. 11, Theorem 4.1, (30)

import Mathlib
import Definitions.Def_auto_M05_f3f59_EthierKurtz_HasCrossVariation
import Definitions.Def_FunctionalIto_Formula_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace FunctionalIto.Formula

/-- Theorem 4.1 (p. 11), the functional Itô formula (30): for every nonanticipative
functional `F ∈ ℂ_b^{1,2}([0,T))` verifying (10) and every `t ∈ [0,T)`, almost surely
`F_t(X_t, A_t) − F_0(X_0, A_0) = ∫_0^t 𝒟_uF(X_u, A_u) du + ∫_0^t ∇_xF_u(X_u, A_u) · dX(u)
  + ½ ∫_0^t tr(∇_x²F_u(X_u, A_u) d[X](u))`, with `d[X](u) = A(u) du` by (3).
The Itô integral is the limit in probability of its dyadic left Riemann sums; the statement
says these sums converge in probability to the remaining terms of (30). -/
theorem theorem_4_1 {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (hU : UsualHypotheses P ℱ) (X V M : ℝ≥0 → Ω → Fin d → ℝ)
    (A : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ) (hS : IsContSemimartingale P ℱ X V M A)
    (T : ℝ≥0) (F DF : Functional d ℝ) (DxF : Functional d (Fin d → ℝ))
    (DxxF : Functional d (Matrix (Fin d) (Fin d) ℝ)) (hF : IsC12b T F DF DxF DxxF)
    (h10 : PredictableInV T F)
    (t : ℝ≥0) (ht : t < T) :
    TendstoInMeasure P
      (fun (n : ℕ) (ω : Ω) => ∑ i, EthierKurtz.itoStepSum (fun s ω => X s ω i) t n
        (fun k ω => DxF ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ n) (fun s => X s ω) (fun s => A s ω) i) ω)
      atTop
      (fun ω => F t (fun s => X s ω) (fun s => A s ω) - F 0 (fun s => X s ω) (fun s => A s ω)
        - (∫ u in (0 : ℝ)..(t : ℝ), DF u.toNNReal (fun s => X s ω) (fun s => A s ω))
        - (1 / 2 : ℝ) * ∫ u in (0 : ℝ)..(t : ℝ),
            Matrix.trace (DxxF u.toNNReal (fun s => X s ω) (fun s => A s ω) * A u.toNNReal ω)) := by sorry

end FunctionalIto.Formula
