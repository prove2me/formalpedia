-- Prove2me | Theorems.Thm_GoldieRenewal_Implicit_Supplement_theorem_5_3
-- name    : GoldieRenewal.Implicit.Supplement.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:16:14.234036+00:00
-- url     : https://prove2.me/theorems/34e42abf-b864-4801-b259-4178ebcc140d
-- title:
--   Theorem 5.3 (corrected: exponent −iθ log t) — rate of approach for R =_L max(Q, MR): both (3.8) and (3.10)
-- statement:
--   Suppose that $R$ solves (1.2), $R\overset{L}{=}\max(Q,MR)$ with $R$ independent of $(M,Q)$, where $M\ge0$ a.s. Let $\kappa>0$ and $\beta>0$, and assume (2.3) $E|M|^\kappa=1$, (3.3) $E|M|^{\kappa+\beta}<\infty$, (3.4) (the conditional law of $\log|M|$ given $M\neq0$ is spread out) and $E(Q^+)^{\kappa+\beta}<\infty$. Suppose that $\eta(dx):=e^{\kappa x}P(\log M\in dx)$ satisfies (3.1) and the subsequent conditions of Theorem 3.1. Then both the upper-tail expansion (3.8) and the lower-tail expansion (3.10) hold:
--   $$
--   t^\kappa P(R>t)=C_+-\frac1{2\pi}\Re\oint_{\mathcal C}e^{-i\theta\log t}\frac{\hat g_1(\theta)}{1-\hat\eta(\theta)}\,d\theta+O(t^{-\beta/2}),
--   $$
--   and the same with $P(R<-t)$, $C_-$, $\hat g_{-1}$, for every admissible contour $\mathcal C$.
--
--   Specialized to the stationary waiting time of a G/G/1 queue this gives an explicit exponential rate in the asymptotics of the waiting-time tail.
--
--   **Formalization Note** "$R$ solves (1.2)" is: $R$ independent of $(Q,M)$ and the law operator of (1.2) for the law of $(Q,M)$ fixes the law of $R$. (3.8) and (3.10) are the published `ExpansionPos`, `ExpansionNeg`. Only $E(Q^+)^{\kappa+\beta}<\infty$ is assumed, as printed. The lower-tail expansion is degenerate here: the solution of (1.2) is nonnegative a.s., so $P(R<-t)=0$, $g_{-1}=0$ and $C_-=0$; it is stated as printed.
--
--   Differences from the source:
--
--   - correction: (3.8), (3.10) carry e^{−iθt} → the exponent is e^{−iθ log t}; reason: the proof of Theorem 3.2 (pp. 154–155) establishes the remainder in the logarithmic variable; the published (3.8), (3.10) are stated this way
--   - reading: 𝒞 as in Theorem 3.1 → every admissible axis-parallel rectangle; reason: the convention of the published Theorem 3.1; the contour integral does not depend on the enclosing contour
--   - encoding: R solves (1.2); moments → IndepFun of R and (Q, M) plus the law operator of (1.2) fixing the law of R; lower Lebesgue integrals; reason: under independence the law of max(Q, MR) is the image of law(Q, M) ⊗ law(R)
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 139, Theorem 5.3; proof p. 159

import Mathlib
import Definitions.Def_GoldieRenewal_Rates_Transforms
import Definitions.Def_GoldieRenewal_Rates_Model
import Definitions.Def_GoldieRenewal_Rates_Expansion
import Definitions.Def_GoldieRenewal_Implicit_Supplement_Models

namespace GoldieRenewal.Implicit.Supplement

open MeasureTheory ProbabilityTheory GoldieRenewal.Rates

/-- **Theorem 5.3** (Goldie, *Implicit renewal theory and tails of solutions of random equations*,
Ann. Appl. Probab. 1(1) (1991), p. 139; rate of approach for the random extremal equation).
Suppose that `R` solves (1.2) `R =_L max(Q, MR)`, `R` independent of `(M, Q)`, where `M ≥ 0`
satisfies (2.3) `E|M|^κ = 1` for some `κ > 0` and, for some `β > 0`, (3.3) `E|M|^{κ+β} < ∞` and
(3.4) hold and `E(Q⁺)^{κ+β} < ∞`. Suppose `η(dx) := e^{κx} P(log M ∈ dx)` satisfies (3.1) and the
subsequent conditions of Theorem 3.1. Then both (3.8) and (3.10) hold.

**Formalization Note** "`R` solves (1.2)" is: `R` independent of `(Q, M)` and `extremalOperator` of
the law of `(Q, M)` fixes the law of `R`. `η` is the published `tiltedLaw`; (3.8), (3.10) are the
published `ExpansionPos`, `ExpansionNeg` (exponent `−iθ log t`). Only `E(Q⁺)^{κ+β} < ∞` is assumed,
as printed. Moments are lower Lebesgue integrals. -/
theorem theorem_5_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Q M R : Ω → ℝ) (hQ : Measurable Q) (hM : Measurable M) (hR : Measurable R)
    (h_indep : IndepFun R (fun ω => (Q ω, M ω)) P)
    (h_fix : extremalOperator (P.map (fun ω => (Q ω, M ω))) (P.map R) = P.map R)
    (hM_nonneg : ∀ᵐ ω ∂P, 0 ≤ M ω)
    (κ β : ℝ) (hκ : 0 < κ) (hβ : 0 < β)
    (h_2_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ κ) ∂P = 1)
    (h_3_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ (κ + β)) ∂P < ⊤)
    (h_3_4 : SpreadOut (logLawGivenNonzero P M))
    (hQ_mom : ∫⁻ ω, ENNReal.ofReal (max (Q ω) 0 ^ (κ + β)) ∂P < ⊤)
    (h_stone : StoneConditions (tiltedLaw P M κ) β) :
    ExpansionPos P M R κ β ∧ ExpansionNeg P M R κ β := by sorry

end GoldieRenewal.Implicit.Supplement
