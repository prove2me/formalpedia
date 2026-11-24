-- Prove2me | Theorems.Thm_GoldieRenewal_Implicit_Supplement_theorem_6_3
-- name    : GoldieRenewal.Implicit.Supplement.theorem_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:17:15.175238+00:00
-- url     : https://prove2.me/theorems/9ff29e40-ae0e-44a5-85dd-7fa8adeabf30
-- title:
--   Theorem 6.3 (corrected: exponent −iθ log t) — rate of approach for R =_L Q + M max(L, R): both (3.8) and (3.10)
-- statement:
--   Suppose $R$ solves (1.3), $R\overset{L}{=}Q+M\max(L,R)$ with $R$ independent of $(L,M,Q)$, where $M\ge0$ a.s. Let $\kappa>0$ and $\beta\in(0,1)$, and assume (2.3) $E|M|^\kappa=1$, (3.3) $E|M|^{\kappa+\beta}<\infty$, (3.4), and
--   $$
--   E|Q|^{\kappa+\beta}<\infty,\qquad E|ML^+|^{\kappa+\beta}<\infty.
--   $$
--   Suppose that $\eta(dx):=e^{\kappa x}P(\log M\in dx)$ satisfies (3.1) and the subsequent conditions of Theorem 3.1. Then both expansions (3.8) (for $t^\kappa P(R>t)$) and (3.10) (for $t^\kappa P(R<-t)$) hold, for every admissible contour.
--
--   This is the rate companion of Theorem 6.2.
--
--   **Formalization Note** "$R$ solves (1.3)" is: $R$ independent of $(Q,M,L)$ and the law operator of (1.3) fixes the law of $R$. (3.8), (3.10) are the published `ExpansionPos`, `ExpansionNeg`. The theorem is stated as printed. Its proof (p. 161) verifies (3.11) only and then cites Theorem 3.2(iii); the lower-tail conclusion (3.10) needs (3.12) there, which the paper does not check for this model.
--
--   Differences from the source:
--
--   - correction: (3.8), (3.10) carry e^{−iθt} → the exponent is e^{−iθ log t}; reason: the proof of Theorem 3.2 (pp. 154–155) establishes the remainder in the logarithmic variable; the published (3.8), (3.10) are stated this way
--   - reading: 𝒞 as in Theorem 3.1 → every admissible axis-parallel rectangle; reason: the convention of the published Theorem 3.1; the contour integral does not depend on the enclosing contour
--   - encoding: R solves (1.3); moments → IndepFun of R and (Q, M, L) plus the law operator of (1.3) fixing the law of R; lower Lebesgue integrals; reason: under independence the law of Q + M max(L, R) is the image of law(Q, M, L) ⊗ law(R)
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 140, Theorem 6.3; proof p. 161

import Mathlib
import Definitions.Def_GoldieRenewal_Rates_Transforms
import Definitions.Def_GoldieRenewal_Rates_Model
import Definitions.Def_GoldieRenewal_Rates_Expansion
import Definitions.Def_GoldieRenewal_Implicit_Supplement_Models

namespace GoldieRenewal.Implicit.Supplement

open MeasureTheory ProbabilityTheory GoldieRenewal.Rates

/-- **Theorem 6.3** (Goldie, *Implicit renewal theory and tails of solutions of random equations*,
Ann. Appl. Probab. 1(1) (1991), p. 140; rate of approach for Letac's model E). Suppose `R` solves
(1.3) `R =_L Q + M max(L, R)`, `R` independent of `(L, M, Q)`, where `M ≥ 0` satisfies (2.3)
`E|M|^κ = 1` for some `κ > 0` and, for some `β ∈ (0, 1)`, (3.3) `E|M|^{κ+β} < ∞` and (3.4) hold and
`E|Q|^{κ+β} < ∞`, `E|ML⁺|^{κ+β} < ∞`. Suppose `η(dx) := e^{κx} P(log M ∈ dx)` satisfies (3.1) and
the subsequent conditions of Theorem 3.1. Then both (3.8) and (3.10) hold.

**Formalization Note** "`R` solves (1.3)" is: `R` independent of `(Q, M, L)` and `letacEOperator`
of the law of `(Q, M, L)` fixes the law of `R`. `η` is the published `tiltedLaw`; (3.8), (3.10) are
the published `ExpansionPos`, `ExpansionNeg`. Stated as printed: the proof (p. 161) checks only
(3.11), so the (3.10) conjunct rests on a step the paper does not carry out (see the moderation
notes). Moments are lower Lebesgue integrals. -/
theorem theorem_6_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Q M L R : Ω → ℝ) (hQ : Measurable Q) (hM : Measurable M) (hL : Measurable L)
    (hR : Measurable R)
    (h_indep : IndepFun R (fun ω => (Q ω, M ω, L ω)) P)
    (h_fix : letacEOperator (P.map (fun ω => (Q ω, M ω, L ω))) (P.map R) = P.map R)
    (hM_nonneg : ∀ᵐ ω ∂P, 0 ≤ M ω)
    (κ β : ℝ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (h_2_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ κ) ∂P = 1)
    (h_3_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ (κ + β)) ∂P < ⊤)
    (h_3_4 : SpreadOut (logLawGivenNonzero P M))
    (hQ_mom : ∫⁻ ω, ENNReal.ofReal (|Q ω| ^ (κ + β)) ∂P < ⊤)
    (hML_mom : ∫⁻ ω, ENNReal.ofReal (|M ω * max (L ω) 0| ^ (κ + β)) ∂P < ⊤)
    (h_stone : StoneConditions (tiltedLaw P M κ) β) :
    ExpansionPos P M R κ β ∧ ExpansionNeg P M R κ β := by sorry

end GoldieRenewal.Implicit.Supplement
