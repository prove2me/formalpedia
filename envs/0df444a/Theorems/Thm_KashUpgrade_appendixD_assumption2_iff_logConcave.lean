-- Prove2me | Theorems.Thm_KashUpgrade_appendixD_assumption2_iff_logConcave
-- name    : KashUpgrade.appendixD_assumption2_iff_logConcave
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:21:58.830373+00:00
-- url     : https://prove2.me/theorems/43544d43-530d-48c6-b296-0a3ed9b34079
-- title:
--   Appendix D, p.51 — Assumption 2 is equivalent to log-concavity of $1-F$
-- statement:
--   Let $f$ be a density of the customer type with support $[0,\zeta]$. Then $(1-F)/f$ is monotonically decreasing on the support if and only if $1-F$ is log-concave, i.e. $\log(1-F)$ is concave on $[0,\zeta)$.
--
--   Log-concavity is the form of Assumption 2 used for the quasiconcavity of the terms of problem (12).
--
--   Differences from the source:
--   - encoding: log-concavity of 1−F as a function of θ → concavity of log(1−F) on [0, ζ); reason: 1−F > 0 there; at a finite ζ the logarithm of 0 would be a junk value in Lean
--   - encoding: (1−F)/f monotonically decreasing on the support, differentiable density f → f > 0 and f differentiable on (0, ζ) as standing hypotheses, (1−F)/f antitone on (0, ζ); reason: Lean has x/0 = 0; see the definition of Assumption 2
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), Appendix D, p.51

import Mathlib
import Definitions.Def_KashUpgrade_Assumption2

namespace KashUpgrade

/-- **Assumption 2 is log-concavity of `1 - F`.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), Appendix D, p.51: for a density with support
`[0, ζ]`, the ratio `(1 - F) / f` is monotonically decreasing on the support if and only if
`1 - F` is log-concave.

**Formalization Note** Log-concavity is stated as concavity of the logarithm on `[0, ζ)`, where
`1 - F > 0`; at a finite `ζ` the logarithm of `0` would be the junk value of `Real.log`. -/
theorem appendixD_assumption2_iff_logConcave {f : ℝ → ℝ} {ζ : ENNReal} (hf : IsTypeDensity f ζ) : AntitoneOn (fun p => (1 - typeCdf f p) / f p) (typeInterior ζ) ↔ ConcaveOn ℝ {θ : ℝ | 0 ≤ θ ∧ ENNReal.ofReal θ < ζ} (fun θ => Real.log (1 - typeCdf f θ)) := by sorry

end KashUpgrade
