-- Prove2me | Theorems.Thm_LearnStability_ConvexSCO_theorem3_first_display
-- name    : LearnStability.ConvexSCO.theorem3_first_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T18:18:23.968629+00:00
-- url     : https://prove2.me/theorems/77160f94-8528-466b-819c-7336576977a1
-- title:
--   Theorem 2 applied to the regularized objective: $R(\hat h_\lambda)\le\inf_h R(h)+4(L+\lambda B)^2/(\delta\lambda m)$ w.p. $1-\delta$
-- statement:
--   Consider a stochastic convex optimization problem on $\mathcal H$ with objective $f(h;z)$ convex and $L$-Lipschitz in $h$, $|f|\le C$, and $\|h\|\le B$ for all $h\in\mathcal H$. For $\lambda>0$ let $r(h;z)=\frac\lambda2\|h\|^2+f(h;z)$ and $R(h)=\mathbb E_z[r(h;z)]=\frac\lambda2\|h\|^2+F(h)$. Let $\hat h_\lambda$ minimize $F_S(h)+\frac\lambda2\|h\|^2$ over $\mathcal H$ (Eq. (5)), chosen measurably in the sample. Then for every distribution $D$, every $m\ge1$ and every $\delta\in(0,1)$, with probability at least $1-\delta$ over $S\sim D^m$,
--   $$\frac\lambda2\|\hat h_\lambda\|^2+F(\hat h_\lambda)\ \le\ \inf_{h\in\mathcal H}\Big(\frac\lambda2\|h\|^2+F(h)\Big)+\frac{4(L+\lambda B)^2}{\delta\lambda m}.$$
--
--   This is Theorem 2 applied to $r$, which is $\lambda$-strongly convex and $(L+\lambda B)$-Lipschitz on $\mathcal H$; it is the first step of the proof of Theorem 3, holding for every fixed $\lambda>0$.
--
--   **Formalization Note** The failure event $\{S:\ \text{right side}<\text{left side}\}$ has $D^m$-probability at most $\delta$. The selection is required to make $(S,z)\mapsto f(\hat h_\lambda;z)$ jointly measurable (series convention).
-- source:
--   Shalev-Shwartz, Shamir, Srebro and Sridharan, Learnability, Stability and Uniform Convergence, JMLR 11 (2010), p. 2645, proof of Theorem 3, first display

import Mathlib
import Definitions.Def_LearnStability_ConvexSCO_Setting
import Definitions.Def_LearnStability_ConvexSCO_Problem

open MeasureTheory

namespace LearnStability.ConvexSCO

/-- Proof of Theorem 3, first display (p. 2645): Theorem 2 applied to the regularized
objective `r(h; z) = (λ/2)‖h‖² + f(h; z)`, which is `λ`-strongly convex and
`(L + λB)`-Lipschitz on `H` when `‖h‖ ≤ B` on `H`. For every `λ > 0`, every distribution
`D`, every `m ≥ 1`, every `δ ∈ (0,1)` and every measurable selection `ĥ_λ` of minimizers of
(5), with probability at least `1 − δ` over `S ∼ D^m`,
`(λ/2)‖ĥ_λ‖² + F(ĥ_λ) ≤ inf_{h ∈ H} ((λ/2)‖h‖² + F(h)) + 4(L + λB)²/(δλm)`. -/
theorem theorem3_first_display {Z E : Type*} [MeasurableSpace Z] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {Hset : Set E} {f : E → Z → ℝ} {L C B : ℝ}
    (hP : IsStochasticConvexProblem Hset f L C) (hB : ∀ h ∈ Hset, ‖h‖ ≤ B)
    {lam : ℝ} (hlam : 0 < lam) (D : Measure Z) [IsProbabilityMeasure D]
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {m : ℕ} (hm : 1 ≤ m)
    (hhat : (Fin m → Z) → E) (hmin : IsRegMinimizerOn Hset f lam hhat)
    (hmeas : IsMeasurableSelection f hhat) :
    sampleLaw D m {S | (⨅ h : Hset, (lam / 2 * ‖(h : E)‖ ^ 2 + risk f D (h : E))) +
        4 * (L + lam * B) ^ 2 / (δ * lam * m) <
        lam / 2 * ‖hhat S‖ ^ 2 + risk f D (hhat S)} ≤ ENNReal.ofReal δ := by sorry

end LearnStability.ConvexSCO
