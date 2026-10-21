-- Prove2me | Theorems.Thm_InhomMJPStrong_J1_doob_step
-- name    : InhomMJPStrong.J1.doob_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:47.748988+00:00
-- url     : https://prove2.me/theorems/dd2b1906-ac37-40ef-a91b-eee14cd1d160
-- title:
--   Proof of Lemma 1, p. 8 — Doob maximal bound for exponential arrivals
-- statement:
--   Let $T_\ell$ be the $\ell$-th arrival time formed from independent rate-$n$ exponential gaps, with $n\ge1$. For $0<\varepsilon<1$, put $m=\lfloor n^{1+\varepsilon}\rfloor$. For every $\beta>0$ and integer $k\ge0$, the maximal deviation of the first $m$ arrival times satisfies
--
--   $$
--   \mathbb P\!\left(
--     \max_{1\le\ell\le m}|T_\ell-\ell/n|\ge\beta
--   \right)
--   \le
--   \frac{\mathbb E[(T_m-m/n)^{2k}]}{\beta^{2k}}.
--   $$
--
--   This is the Doob maximal-inequality step used in the proof of Lemma 1. It applies to either of the paper's rate-$n$ grids once their superposition law is established.
--
--   **Formalization Note** The statement is generalized from the paper's observation-grid arrivals $\theta^{(n)}$ to any sequence with independent rate-$n$ exponential gaps. The probability on the left is read as an outer measure; the moment exists under the exponential-gap assumptions.
-- source:
--   Bladt & Peralta, Strongly convergent homogeneous approximations to inhomogeneous Markov jump processes and applications, arXiv:2204.02954v3, p. 8, proof of Lemma 1, Doob display following (15)

import Mathlib
import Definitions.Def_InhomMJPStrong_J1_Model

namespace InhomMJPStrong.J1

open MeasureTheory ProbabilityTheory Filter

/-- The maximal-inequality step in the proof of Lemma 1, p. 8. -/
theorem doob_step {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n) (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1)
    (g : ℕ → Ω → ℝ) (hgIndep : iIndepFun g P)
    (hgLaw : ∀ i, HasLaw (g i) (expMeasure (n : ℝ)) P)
    (beta : ℝ) (hbeta : 0 < beta) (k : ℕ) :
    let m := gridSize n eps
    let T : Ω → ℕ → ℝ := fun ω l => arrival (fun i => g i ω) l
    P {ω | beta ≤ maxGap (T ω) (fun l => (l : ℝ) / (n : ℝ)) m} ≤
      ENNReal.ofReal
        ((∫ ω, (T ω m - (m : ℝ) / (n : ℝ)) ^ (2 * k) ∂P) /
          beta ^ (2 * k)) := by sorry

end InhomMJPStrong.J1
