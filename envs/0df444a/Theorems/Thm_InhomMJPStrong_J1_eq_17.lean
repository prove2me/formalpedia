-- Prove2me | Theorems.Thm_InhomMJPStrong_J1_eq_17
-- name    : InhomMJPStrong.J1.eq_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:53.344513+00:00
-- url     : https://prove2.me/theorems/00287b77-1623-4a4f-8b5d-c7db86ecb1f9
-- title:
--   Equation (17), p. 9 — equal small tails for both Poisson grids
-- statement:
--   In the common-clock construction, take $q>0$, $0<\varepsilon<1$, $m_n=\lfloor n^{1+\varepsilon}\rfloor$, and
--   $\beta_n=2e^{1/2+\varepsilon/2+2q}(\log n)n^{-1/2+\varepsilon/2}$. For $n\ge\lambda_0$, the two maximal-deviation events have the same probability, and their common probability is little-$o$ of $n^{-q}$:
--
--   $$
--   \mathbb P\!\left(
--     \max_{1\le\ell\le m_n}|\theta^{(n)}_\ell-\ell/n|\ge\beta_n
--   \right)
--   =
--   \mathbb P\!\left(
--     \max_{1\le\ell\le m_n}|\chi^{(n)}_\ell-\ell/n|\ge\beta_n
--   \right)
--   =o(n^{-q}).
--   $$
--
--   Equation (17) supplies the two one-grid deviations from which Lemma 1 controls their difference.
--
--   **Formalization Note** Equality is asserted for the finite-$n$ range $n\ge\lambda_0$ where both superpositions have the stated rate. The little-$o$ statement concerns $n\to\infty$.
-- source:
--   Bladt & Peralta, Strongly convergent homogeneous approximations to inhomogeneous Markov jump processes and applications, arXiv:2204.02954v3, p. 9, proof of Lemma 1, equation (17)

import Mathlib
import Definitions.Def_InhomMJPStrong_J1_Model

namespace InhomMJPStrong.J1

open MeasureTheory ProbabilityTheory Filter Asymptotics

/-- Equation (17), p. 9: the two grid deviations have the same small tail. -/
theorem eq_17 {p : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (hp : 1 ≤ p) (Lam : ℝ → Matrix (Fin p) (Fin p) ℝ)
    (hLam : IsIntensityFn Lam) (hBound : Condition1 Lam)
    (hPos : 0 < sSup {x : ℝ | ∃ i t, 0 ≤ t ∧ x = |Lam t i i|})
    (alpha : Fin p → ℝ) (hAlpha : (∀ i, 0 ≤ alpha i) ∧ ∑ i, alpha i = 1)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Src → Ω → ℝ) (hX : IsUnifSetup (lam0 Lam) X P)
    (q eps : ℝ) (hq : 0 < q) (heps : 0 < eps) (heps1 : eps < 1) :
    let beta : ℕ → ℝ := fun n =>
      2 * Real.exp (1 / 2 + eps / 2 + 2 * q) * Real.log (n : ℝ) *
        (n : ℝ) ^ (-(1 : ℝ) / 2 + eps / 2)
    (∀ n, lam0 Lam ≤ n →
      P {ω | beta n ≤
        maxGap (theta (lam0 Lam) n X ω)
          (fun l => (l : ℝ) / (n : ℝ)) (gridSize n eps)} =
      P {ω | beta n ≤
        maxGap (chi (lam0 Lam) n X ω)
          (fun l => (l : ℝ) / (n : ℝ)) (gridSize n eps)}) ∧
    (fun n : ℕ =>
      (P {ω | beta n ≤
        maxGap (theta (lam0 Lam) n X ω)
          (fun l => (l : ℝ) / (n : ℝ)) (gridSize n eps)}).toReal)
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-q)) := by sorry

end InhomMJPStrong.J1
