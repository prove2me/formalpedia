-- Prove2me | Theorems.Thm_LRTempElim_eq_136
-- name    : LRTempElim.eq_136
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:27:13.65104+00:00
-- url     : https://prove2.me/theorems/54a9d1db-a8d5-4256-b806-93f931bf2686
-- title:
--   Eq. (136): $I_a\sim\frac{\pi^3}{2\sqrt{2\pi}\,a^3}e^{-a^2/8}$ and $1/I_a\sim\frac{2\sqrt{2\pi}}{\pi^3}a^3e^{a^2/8}$
-- statement:
--   Let $I_a=\mathbb E_{\nu_a}[X^2\sigma(aX)(1-\sigma(aX))]$. As $a\to\infty$,
--   $$
--   I_a\sim\frac{\pi^3}{2\sqrt{2\pi}\,a^3}\,e^{-a^2/8},\qquad \frac1{I_a}\sim\frac{2\sqrt{2\pi}}{\pi^3}\,a^3e^{a^2/8}.
--   $$
--
--   Combined with the decoupling bound $C_{\mathrm{NCE}}(a)\ge(1+a^2/4)/(2I_a)$, the second relation gives the exponential lower order $a^5e^{a^2/8}$ of the goal theorem.
--
--   **Formalization Note** $f\sim g$ is asymptotic equivalence (`Asymptotics.IsEquivalent`) along $a\to+\infty$ over the reals.
--
--   Differences from the source:
--   - encoding: f ∼ g for large a → `Asymptotics.IsEquivalent atTop f g`; reason: the standard meaning of ∼ as a → +∞
-- source:
--   Chen, Wu, Yang, Zeng, Likelihood-Ratio Learning under Weak Overlap via Analytic Temporal Elimination, STOC 2027 submission (manuscript of 2026-11-03, sha256 eee651394d60e9274fc77c5a1bd08841eb53ee6030924de85b47f5a195371758), §B.3.3, eq. (136), p.41 (pdf p.43)

import Mathlib
import Definitions.Def_LRTempElim_Logistic

open MeasureTheory ProbabilityTheory Filter Asymptotics

namespace LRTempElim

/-- **Eq. (136)**: asymptotics of the logistic information. Chen, Wu, Yang, Zeng,
*Likelihood-Ratio Learning under Weak Overlap via Analytic Temporal Elimination*, STOC 2027
submission (manuscript of 2026-11-03, sha256 eee65139…), §B.3.3, eq. (136), p.41 (pdf p.43).

"For large a, `I_a ∼ π³/(2√(2π) a³) e^{−a²/8}`, `1/I_a ∼ (2√(2π)/π³) a³e^{a²/8}`. (136)"

**Formalization Note.** `∼` is `Asymptotics.IsEquivalent` along `a → +∞` (`atTop` on `ℝ`).
`I_a = E_{ν_a}[X²σ(aX)(1 − σ(aX))]` (`Ia`). -/
theorem eq_136 :
    IsEquivalent atTop Ia
        (fun a => Real.pi ^ 3 / (2 * Real.sqrt (2 * Real.pi) * a ^ 3) * Real.exp (-a ^ 2 / 8)) ∧
      IsEquivalent atTop (fun a => 1 / Ia a)
        (fun a => 2 * Real.sqrt (2 * Real.pi) / Real.pi ^ 3 * a ^ 3 *
          Real.exp (a ^ 2 / 8)) := by sorry

end LRTempElim
