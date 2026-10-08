-- Prove2me | Theorems.Thm_FunctionalIto_Formula_theorem_4_1_bounded
-- name    : FunctionalIto.Formula.theorem_4_1_bounded
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:11:20.186857+00:00
-- url     : https://prove2.me/theorems/56dc2fa2-65a8-4c5b-8a69-fdcf71cb4f4f
-- title:
--   Proof of Theorem 4.1, pp. 11–13 — the functional Itô formula when X stays in a compact set and ‖A‖∞ ≤ R
-- statement:
--   Assume the setting of §2 and let $F\in\mathbb C^{1,2}_b([0,T))$ verify (10), with derivatives $\mathcal DF,\nabla_xF,\nabla_x^2F$. Assume moreover that $X$ does not exit a compact set $K\subset\mathbb R^d$ and that $\|A\|_\infty\le R$ for some $R>0$ on $[0,T]$. Then for every $t\in[0,T)$, almost surely,
--   $$F_t(X_t,A_t)-F_0(X_0,A_0)=\int_0^t\mathcal D_uF(X_u,A_u)\,du+\int_0^t\nabla_xF_u(X_u,A_u)\cdot dX(u)+\frac12\int_0^t\operatorname{tr}\big(\nabla_x^2F_u(X_u,A_u)\,A(u)\big)\,du .$$
--
--   This is the first step of the proof of Theorem 4.1; the general case follows by localization.
--
--   **Formalization Note.** As in the goal theorem, the stochastic integral is the limit in probability of its dyadic left Riemann sums $\sum_{k<2^n}\nabla_xF_{t_k}(X_{t_k},A_{t_k})\cdot(X(t_{k+1})-X(t_k))$, $t_k=kt/2^n$, and the statement says that these sums converge in probability to the other terms of the identity. $d[X](u)=A(u)\,du$ by (3). $\|A\|_\infty\le R$ is read entrywise.
-- source:
--   Cont and Fournié, Functional Itô calculus and stochastic integral representation of martingales, arXiv:1002.2446v5, pp. 11–13, proof of Theorem 4.1 ("Let us first assume that X does not exit a compact set K and that ‖A‖∞ ≤ R")

import Mathlib
import Definitions.Def_auto_M05_f3f59_EthierKurtz_HasCrossVariation
import Definitions.Def_FunctionalIto_Formula_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace FunctionalIto.Formula

/-- Theorem 4.1 in the bounded case treated first in its proof (pp. 11–13): if moreover `X`
stays in a compact set `K` and `‖A‖_∞ ≤ R` (entrywise) on `[0,T]`, then for every `t < T`, (30) holds:
the dyadic left Riemann sums of the Itô integral `∫_0^t ∇_xF_u(X_u, A_u) · dX(u)` converge in
probability to
`F_t(X_t, A_t) − F_0(X_0, A_0) − ∫_0^t 𝒟_uF(X_u, A_u) du − ½ ∫_0^t tr(∇_x²F_u(X_u, A_u) A(u)) du`. -/
theorem theorem_4_1_bounded {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (hU : UsualHypotheses P ℱ) (X V M : ℝ≥0 → Ω → Fin d → ℝ)
    (A : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ) (hS : IsContSemimartingale P ℱ X V M A)
    (T : ℝ≥0) (F DF : Functional d ℝ) (DxF : Functional d (Fin d → ℝ))
    (DxxF : Functional d (Matrix (Fin d) (Fin d) ℝ)) (hF : IsC12b T F DF DxF DxxF)
    (h10 : PredictableInV T F)
    (K : Set (Fin d → ℝ)) (hK : IsCompact K) (hXK : ∀ s ≤ T, ∀ ω, X s ω ∈ K)
    (R : ℝ) (hR : 0 < R) (hAR : ∀ s ≤ T, ∀ ω i j, |A s ω i j| ≤ R)
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
