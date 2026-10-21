-- Prove2me | Theorems.Thm_InhomMJPStrong_J1_eq_16
-- name    : InhomMJPStrong.J1.eq_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:53.695658+00:00
-- url     : https://prove2.me/theorems/cae64cc4-a45f-4894-bb6e-c760bd33143d
-- title:
--   Equation (16), p. 9 — explicit maximal-deviation probability bound
-- statement:
--   Let $T_\ell$ be the arrival times of independent rate-$n$ exponential gaps. Suppose $n\ge e^2$, $0<\varepsilon<1$, and $C\ge1$, and put $m=\lfloor n^{1+\varepsilon}\rfloor$ and $\beta_n=2C(\log n)n^{-1/2+\varepsilon/2}$. Then the final inequality of (16) is
--
--   $$
--   \mathbb P\!\left(
--     \max_{1\le\ell\le m}|T_\ell-\ell/n|\ge\beta_n
--   \right)
--   \le\frac{2\sqrt{n^{1+\varepsilon}}}{C^{\log n}}.
--   $$
--
--   This makes the dependence on the adjustable constant $C$ explicit, preparing the little-$o$ conclusion in (17).
--
--   **Formalization Note** The paper writes the observation-grid times $\theta^{(n)}$; the statement holds for any independent rate-$n$ exponential gap sequence. The threshold and the last bound of (16) are preserved exactly.
-- source:
--   Bladt & Peralta, Strongly convergent homogeneous approximations to inhomogeneous Markov jump processes and applications, arXiv:2204.02954v3, p. 9, proof of Lemma 1, equation (16)

import Mathlib
import Definitions.Def_InhomMJPStrong_J1_Model

namespace InhomMJPStrong.J1

open MeasureTheory ProbabilityTheory

/-- The final probability estimate of equation (16), p. 9. -/
theorem eq_16 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : Real.exp 2 ≤ (n : ℝ))
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1)
    (g : ℕ → Ω → ℝ) (hgIndep : iIndepFun g P)
    (hgLaw : ∀ i, HasLaw (g i) (expMeasure (n : ℝ)) P)
    (C : ℝ) (hC : 1 ≤ C) :
    let m := gridSize n eps
    let beta := 2 * C * Real.log (n : ℝ) *
      (n : ℝ) ^ (-(1 : ℝ) / 2 + eps / 2)
    P {ω | beta ≤
      maxGap (fun l => arrival (fun i => g i ω) l)
        (fun l => (l : ℝ) / (n : ℝ)) m} ≤
      ENNReal.ofReal
        (2 * Real.sqrt ((n : ℝ) ^ (1 + eps)) / C ^ Real.log (n : ℝ)) := by sorry

end InhomMJPStrong.J1
