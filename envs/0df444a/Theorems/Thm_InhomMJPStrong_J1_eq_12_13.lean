-- Prove2me | Theorems.Thm_InhomMJPStrong_J1_eq_12_13
-- name    : InhomMJPStrong.J1.eq_12_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:57.5467+00:00
-- url     : https://prove2.me/theorems/5d055576-e1dc-4413-a7ae-aaedd6455f88
-- title:
--   Equations (12)–(13), p. 8 — time change aligns the paths almost surely
-- statement:
--   Fix $\varepsilon>0$ and $n\ge\lambda_0$, and set $m=\lfloor n^{1+\varepsilon}\rfloor$. Define $\Delta_n$ by linear interpolation between the matching grid knots
--   $\Delta_n(\chi^{(n)}_\ell)=\theta^{(n)}_\ell$ for $0\le\ell\le m$, followed by a ray of slope one. Almost surely, $\Delta_n$ is continuous and strictly increasing, starts at zero, and tends to infinity. Moreover,
--
--   $$
--   J^{(n)}(\Delta_n(s))=\mathcal J(s)
--   \qquad(0\le s<\chi^{(n)}_m).
--   $$
--
--   This is the pathwise alignment used in the $J_1$ comparison. The first interpolation segment and the last unit-slope ray are the cases displayed in equation (12).
--
--   **Formalization Note** The paper's claim that $\Delta_n$ is homeomorphic and that (13) holds is read almost surely, as its surrounding text specifies. The time change is real-valued on nonnegative real times; it is converted to a nonnegative real before evaluating $J^{(n)}$.
-- source:
--   Bladt & Peralta, Strongly convergent homogeneous approximations to inhomogeneous Markov jump processes and applications, arXiv:2204.02954v3, p. 8, Step (2), equations (12)–(13)

import Mathlib
import Definitions.Def_InhomMJPStrong_J1_Model

namespace InhomMJPStrong.J1

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

/-- Equations (12)–(13), p. 8: the grid-matching time change and the pathwise coupling. -/
theorem eq_12_13 {p : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (hp : 1 ≤ p) (Lam : ℝ → Matrix (Fin p) (Fin p) ℝ)
    (hLam : IsIntensityFn Lam) (hBound : Condition1 Lam)
    (hPos : 0 < sSup {x : ℝ | ∃ i t, 0 ≤ t ∧ x = |Lam t i i|})
    (alpha : Fin p → ℝ) (hAlpha : (∀ i, 0 ≤ alpha i) ∧ ∑ i, alpha i = 1)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Src → Ω → ℝ) (hX : IsUnifSetup (lam0 Lam) X P)
    (n : ℕ) (hn : lam0 Lam ≤ n) (eps : ℝ) (heps : 0 < eps) :
    ∀ᵐ ω ∂P,
      let m := gridSize n eps
      let D : ℝ≥0 → ℝ := fun s =>
        timeChange (chi (lam0 Lam) n X ω) (theta (lam0 Lam) n X ω) m (s : ℝ)
      StrictMono D ∧ Continuous D ∧ D 0 = 0 ∧
      Tendsto D atTop atTop ∧
      ∀ s : ℝ≥0, (s : ℝ) < chi (lam0 Lam) n X ω m →
        procJn Lam alpha X n ω (Real.toNNReal (D s)) = procJ Lam alpha X ω s := by sorry

end InhomMJPStrong.J1
