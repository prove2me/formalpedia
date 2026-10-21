-- Prove2me | Theorems.Thm_InhomMJPStrong_J1_theorem_3
-- name    : InhomMJPStrong.J1.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:00:13.488764+00:00
-- url     : https://prove2.me/theorems/032c2d21-af92-4785-bf09-b38989e5399e
-- title:
--   Theorem 3, p. 9 — quantitative strong J1 convergence
-- statement:
--   Let $\mathcal J$ be the uniformized finite-state jump process of Step (1), and let $J^{(n)}$ be its coupled approximation sampled on the inspection grid and placed on an independent observation grid. Assume the paper's intensity-matrix conditions, Condition 1, a probability initial distribution, and the independent Poisson clocks and uniforms. For every $q>0$ and $0<\varepsilon<1$, there is a nonnegative sequence $c_k\to\infty$ such that
--
--   $$
--   \mathbb P\!\left(
--     d_{J_1}(J^{(n)},\mathcal J)
--     \ge 3\kappa(q,\varepsilon)(\log n)n^{-1/2+\varepsilon/2}
--   \right)=o(n^{-q}),
--   \qquad
--   \kappa(q,\varepsilon)=4e^{1/2+\varepsilon/2+2q}.
--   $$
--
--   With this same $c_k$ in the metric, $d_{J_1}(J^{(n)},\mathcal J)\to0$ almost surely. Thus the constructed approximations converge strongly in the $J_1$ topology while the probability of exceeding the displayed rate is smaller than every fixed multiple of $n^{-q}$ eventually.
--
--   **Formalization Note** The standing assumptions are explicit in Lean. The added condition $\sup_{i,t\ge0}|\Lambda_{ii}(t)|>0$ excludes the zero-rate case, for which the paper's $\lambda_0^{-1}$ and rate-$\lambda_0$ exponential gaps are undefined. The cemetery state is included; probabilities of potentially nonmeasurable metric events are read as outer measures. The metric is the full formula (3), with the infimum over all homeomorphisms and both its state and time terms.
-- source:
--   Bladt & Peralta, Strongly convergent homogeneous approximations to inhomogeneous Markov jump processes and applications, arXiv:2204.02954v3, p. 9, Theorem 3 (18), proof pp. 9–10

import Mathlib
import Definitions.Def_InhomMJPStrong_J1_Model

namespace InhomMJPStrong.J1

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics

/-- Theorem 3, p. 9: quantitative J1 strong convergence of the constructed Poisson-grid approximation. -/
theorem theorem_3 {p : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (hp : 1 ≤ p) (Lam : ℝ → Matrix (Fin p) (Fin p) ℝ)
    (hLam : IsIntensityFn Lam) (hBound : Condition1 Lam)
    (hPos : 0 < sSup {x : ℝ | ∃ i t, 0 ≤ t ∧ x = |Lam t i i|})
    (alpha : Fin p → ℝ) (hAlpha : (∀ i, 0 ≤ alpha i) ∧ ∑ i, alpha i = 1)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Src → Ω → ℝ) (hX : IsUnifSetup (lam0 Lam) X P)
    (q eps : ℝ) (hq : 0 < q) (heps : 0 < eps) (heps1 : eps < 1) :
    ∃ c : ℕ → ℝ,
      (∀ k, 0 ≤ c k) ∧ Tendsto c atTop atTop ∧
      (fun n : ℕ =>
        (P {ω | ENNReal.ofReal
          (3 * kappa q eps * Real.log (n : ℝ) *
            (n : ℝ) ^ (-(1 : ℝ) / 2 + eps / 2)) ≤
          dJ1 c (procJn Lam alpha X n ω) (procJ Lam alpha X ω)}).toReal)
        =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-q)) ∧
      (∀ᵐ ω ∂P,
        Tendsto (fun n : ℕ => dJ1 c (procJn Lam alpha X n ω) (procJ Lam alpha X ω))
          atTop (𝓝 0)) := by sorry

end InhomMJPStrong.J1
