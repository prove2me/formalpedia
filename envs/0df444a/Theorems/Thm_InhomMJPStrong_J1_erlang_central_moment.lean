-- Prove2me | Theorems.Thm_InhomMJPStrong_J1_erlang_central_moment
-- name    : InhomMJPStrong.J1.erlang_central_moment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:52.209084+00:00
-- url     : https://prove2.me/theorems/4b23d7ec-1a21-43df-bff8-3b1ea4884757
-- title:
--   Proof of Lemma 1, p. 8 — cited Erlang central-moment bounds
-- statement:
--   Let $T_m$ be the sum of $m=\lfloor n^{1+\varepsilon}\rfloor$ independent rate-$n$ exponential gaps, with $n\ge4$ and $0<\varepsilon<1$. Set $r=\sqrt m$. For every integer $k\ge0$, the central moment is bounded by the two inequalities quoted in the paper:
--
--   $$
--   \mathbb E[(T_m-m/n)^{2k}]
--   \le \frac{(2k)!r}{n^{2k}}\frac{r^{2k+1}-1}{r-1}
--   \le 2r\left(\frac{2kr}{n}\right)^{2k}.
--   $$
--
--   The first inequality is invoked from Lemma A.1 of the paper's reference [45]; the second is the elementary simplification printed immediately afterward. Together they provide the moment estimate needed for the probability bound (16).
--
--   **Formalization Note** This uses a generic independent rate-$n$ exponential arrival sequence in place of $\theta^{(n)}$. At $k=0$, Lean evaluates $0^0=1$, matching the intended bound. The condition $n\ge4$ keeps $r-1$ positive.
-- source:
--   Bladt & Peralta, Strongly convergent homogeneous approximations to inhomogeneous Markov jump processes and applications, arXiv:2204.02954v3, pp. 8–9, proof of Lemma 1, cited Lemma A.1 of [45] and the following display

import Mathlib
import Definitions.Def_InhomMJPStrong_J1_Model

namespace InhomMJPStrong.J1

open MeasureTheory ProbabilityTheory

/-- The two Erlang central-moment bounds quoted in the proof of Lemma 1, p. 8. -/
theorem erlang_central_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 4 ≤ n) (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1)
    (g : ℕ → Ω → ℝ) (hgIndep : iIndepFun g P)
    (hgLaw : ∀ i, HasLaw (g i) (expMeasure (n : ℝ)) P) (k : ℕ) :
    let m := gridSize n eps
    let r := Real.sqrt (m : ℝ)
    let moment := ∫ ω, (arrival (fun i => g i ω) m - (m : ℝ) / (n : ℝ)) ^ (2 * k) ∂P
    moment ≤ ((2 * k).factorial : ℝ) * r / (n : ℝ) ^ (2 * k) *
      ((r ^ (2 * k + 1) - 1) / (r - 1)) ∧
    ((2 * k).factorial : ℝ) * r / (n : ℝ) ^ (2 * k) *
      ((r ^ (2 * k + 1) - 1) / (r - 1)) ≤
      2 * r * (2 * (k : ℝ) * r / (n : ℝ)) ^ (2 * k) := by sorry

end InhomMJPStrong.J1
