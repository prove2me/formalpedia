-- Prove2me | Theorems.Thm_OptInapprox_Bal2Sat_theorem_4
-- name    : OptInapprox.Bal2Sat.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:10.080159+00:00
-- url     : https://prove2.me/theorems/ed56ed14-164f-4571-9d7d-fdf8ed97b6ce
-- title:
--   Theorem 4, p. 12 — Balanced-MAX-2SAT: hyperplane rounding of any (SDP − ε)-optimal vector solution has expected weight ≥ β(OPT − ε)
-- statement:
--   **Theorem 4** of Khot, Kindler, Mossel and O'Donnell states that Balanced-MAX-2SAT is polynomial-time approximable to within any factor smaller than $\beta = \min_{\pi/2\le\theta\le\pi}\frac{2+(2/\pi)\theta}{3-\cos\theta} \approx 0.943$. This item states the approximation guarantee of the paper's algorithm.
--
--   Let $I$ be a balanced (Definition 12) weighted MAX-2SAT instance on $n$ variables with nonnegative weights, let $\varepsilon \ge 0$, and let $v_0,\dots,v_{n-1} \in \mathbb R^d$ be any unit vectors whose relaxed objective is within $\varepsilon$ of the optimum of the semidefinite program:
--   $$
--   \mathrm{SDPobj}(v) \ge \mathrm{SDP} - \varepsilon .
--   $$
--   Let $g$ be a standard Gaussian random vector in $\mathbb R^d$ (independent $N(0,1)$ coordinates on some probability space), and round by $x_i = \operatorname{sgn}(g \cdot v_i)$. Then the satisfied weight of the rounded assignment is integrable and
--   $$
--   \mathbb E\bigl[\mathrm{sat}(x)\bigr] \;\ge\; \beta\,(\mathrm{OPT} - \varepsilon).
--   $$
--
--   Since the semidefinite program can be solved to within any $\varepsilon > 0$ in polynomial time, and $\mathrm{OPT} \ge \frac12\sum_C w_C$, this yields the approximation within any factor smaller than $\beta$; combined with Theorem 3 (UGC-hardness of MAX-2SAT beyond $\beta$, which holds even for balanced instances) it shows that $\beta$ is the exact approximability threshold of Balanced-MAX-2SAT under the Unique Games Conjecture.
--
--   **Formalization Note** Polynomial running time is not formalized: the statement is the guarantee the rounding achieves on any $(\mathrm{SDP}-\varepsilon)$-optimal vector solution, which is the part of the theorem proved in §9 (the paper obtains such a solution in polynomial time by citing Goemans–Williamson). The vectors may live in any dimension $d$; $\mathrm{SDP}$ is the supremum over all dimensions. The Gaussian vector is given by the referenced predicate `IsStandardGaussianVector` (measurable, independent coordinates, each of law `gaussianReal 0 1`); the expectation is the Bochner integral, and its integrability is part of the conclusion. The rounding sets $x_i = 1$ when $g\cdot v_i = 0$, an event of probability $0$.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), p. 12, Theorem 4; proof in §9, pp. 21–22

import Mathlib
import Definitions.Def_HighDimProb_RandomVectors_IsStandardGaussianVector
import Definitions.Def_OptInapprox_Bal2Sat_Setting

open MeasureTheory ProbabilityTheory HighDimProb.RandomVectors

namespace OptInapprox.Bal2Sat

/-- Theorem 4, p. 12 (proof §9, pp. 21–22): Balanced-MAX-2SAT is approximable to within any
factor smaller than `β`. The approximation guarantee of the algorithm: for a balanced weighted
instance `I`, any `ε ≥ 0`, and any unit-vector family `v` (in any dimension `d`) achieving
`SDP − ε`, rounding with a standard Gaussian vector `g` (`xᵢ = sgn(g · vᵢ)`) gives an
integrable satisfied weight whose expectation is at least `β (OPT − ε)`. -/
theorem theorem_4 {n : ℕ} (I : Instance n) (hbal : IsBalanced I)
    (ε : ℝ) (hε : 0 ≤ ε) {d : ℕ} (v : Fin n → Fin d → ℝ) (hv : IsUnitFamily v)
    (hnear : sdpValue I - ε ≤ sdpObj I v)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Fin d → Ω → ℝ) (hg : IsStandardGaussianVector P g) :
    Integrable (fun ω => satWeight I (round v (fun k => g k ω))) P ∧
      beta * (OPT I - ε) ≤ ∫ ω, satWeight I (round v (fun k => g k ω)) ∂P := by sorry

end OptInapprox.Bal2Sat
