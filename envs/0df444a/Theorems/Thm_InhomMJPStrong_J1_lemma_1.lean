-- Prove2me | Theorems.Thm_InhomMJPStrong_J1_lemma_1
-- name    : InhomMJPStrong.J1.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:49.349828+00:00
-- url     : https://prove2.me/theorems/805ff5aa-3086-41ba-bb15-555d66be56dd
-- title:
--   Lemma 1, p. 8 — maximal discrepancy of the two Poisson grids
-- statement:
--   Under the intensity-matrix and independent-clock assumptions of Step (1), let $q>0$ and $0<\varepsilon<1$. Put $m_n=\lfloor n^{1+\varepsilon}\rfloor$ and $\kappa(q,\varepsilon)=4e^{1/2+\varepsilon/2+2q}$. Then
--
--   $$
--   \mathbb P\!\left(
--     \max_{1\le\ell\le m_n}
--     |\theta^{(n)}_\ell-\chi^{(n)}_\ell|
--     \ge\kappa(q,\varepsilon)(\log n)n^{-1/2+\varepsilon/2}
--   \right)=o(n^{-q}).
--   $$
--
--   This is the probabilistic control on the time displacement used in the $J_1$ rate theorem.
--
--   **Formalization Note** Lemma 1 states existence of a positive $\kappa(q,\varepsilon)$; its proof on page 9 fixes the displayed value, which is used here and in Theorem 3. Probability is evaluated as an outer measure so that the formal statement does not presuppose measurability of the maximal-deviation event.
-- source:
--   Bladt & Peralta, Strongly convergent homogeneous approximations to inhomogeneous Markov jump processes and applications, arXiv:2204.02954v3, pp. 8–9, Lemma 1 (15) and end of its proof

import Mathlib
import Definitions.Def_InhomMJPStrong_J1_Model

namespace InhomMJPStrong.J1

open MeasureTheory ProbabilityTheory Filter Asymptotics

/-- Lemma 1, p. 8, with the explicit constant fixed in its proof on p. 9. -/
theorem lemma_1 {p : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (hp : 1 ≤ p) (Lam : ℝ → Matrix (Fin p) (Fin p) ℝ)
    (hLam : IsIntensityFn Lam) (hBound : Condition1 Lam)
    (hPos : 0 < sSup {x : ℝ | ∃ i t, 0 ≤ t ∧ x = |Lam t i i|})
    (alpha : Fin p → ℝ) (hAlpha : (∀ i, 0 ≤ alpha i) ∧ ∑ i, alpha i = 1)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Src → Ω → ℝ) (hX : IsUnifSetup (lam0 Lam) X P)
    (q eps : ℝ) (hq : 0 < q) (heps : 0 < eps) (heps1 : eps < 1) :
    (fun n : ℕ =>
      (P {ω | kappa q eps * Real.log (n : ℝ) *
        (n : ℝ) ^ (-(1 : ℝ) / 2 + eps / 2) ≤
        maxGap (theta (lam0 Lam) n X ω) (chi (lam0 Lam) n X ω)
          (gridSize n eps)}).toReal)
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-q)) := by sorry

end InhomMJPStrong.J1
