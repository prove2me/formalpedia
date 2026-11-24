-- Prove2me | Theorems.Thm_GoldieRenewal_Implicit_Supplement_theorem_4_7
-- name    : GoldieRenewal.Implicit.Supplement.theorem_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:14:05.201223+00:00
-- url     : https://prove2.me/theorems/af327721-872d-4e0c-9159-39f42402c6a3
-- title:
--   Theorem 4.7 (corrected: exponent −iθ log t) — rate of approach for R =_L Q + MR: (3.8) and (3.10) if M ≥ 0 a.s., otherwise (3.17) for both tails
-- statement:
--   Let $(Q,M)$ be random coefficients and suppose that $R$ solves the random difference equation (1.1),
--   $$
--   R\overset{L}{=}Q+MR,\qquad R \text{ independent of } (M,Q).
--   $$
--   Let $\kappa>0$ and $\beta\in(0,1)$, and assume (2.3) $E|M|^\kappa=1$, (3.3) $E|M|^{\kappa+\beta}<\infty$, (3.4) (the conditional law of $\log|M|$ given $M\ne0$ is spread out), and $E|Q|^{\kappa+\beta}<\infty$.
--
--   1. If $M\ge0$ a.s., let $\eta(dx):=e^{\kappa x}P(\log M\in dx)$. If $\eta$ satisfies (3.1) and the subsequent conditions of Theorem 3.1, then both expansions (3.8) for $t^\kappa P(R>t)$ and (3.10) for $t^\kappa P(R<-t)$ hold.
--   2. If $P(M<0)>0$, let $\eta$ be the ladder law (3.15) and assume (3.16) $E\,M^{\kappa+\beta}\mathbf 1_{M>0}<1$. If $\eta$ satisfies (3.1) and the subsequent conditions of Theorem 3.1, then (3.17) holds for $t^\kappa P(R>t)$, and $t^\kappa P(R<-t)$ satisfies the same formula.
--
--   This gives the rate of approach in Kesten's power-law tail for the random difference equation (Theorem 4.1).
--
--   **Formalization Note** "$R$ solves (1.1)" is: $R$ is independent of $(Q,M)$ and the law of $R$ is a fixed point of the published law operator `GoldieRenewal.Kesten.rdeOperator` for the law of $(Q,M)$. (3.8) and (3.10) are the published `ExpansionPos` and `ExpansionNeg`; (3.17) and its lower-tail form are `ExpansionSignedPos` and `ExpansionSignedNeg`. Moments are lower Lebesgue integrals.
--
--   Differences from the source:
--
--   - correction: (3.8), (3.10) and (3.17) carry e^{−iθt} in the contour integral → the exponent is e^{−iθ log t}; reason: the proofs (pp. 154–156) establish the remainder in the logarithmic variable; the published (3.8), (3.10) are stated the same way
--   - reading: t^κP(R < −t) satisfies the same formula → (3.17) for −R, i.e. ĝ₁ and ĝ₋₁ exchanged, with the common constant (2.14); reason: as in Theorem 3.3, whose proof says 'for −R in place of R' (p. 156); C₊ = C₋ when P(M < 0) > 0
--   - reading: 𝒞 as in Theorem 3.1 → every admissible axis-parallel rectangle; reason: the convention of the published Theorem 3.1; the contour integral does not depend on the enclosing contour
--   - encoding: R solves (1.1); moments E|·| → IndepFun of R and (Q, M) plus the published rdeOperator fixing the law of R; lower Lebesgue integrals; reason: under independence the law of Q + MR is the image of law(Q, M) ⊗ law(R); no instance changes
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 138, Theorem 4.7

import Mathlib
import Definitions.Def_GoldieRenewal_Kesten_RandomDifferenceEquation
import Definitions.Def_GoldieRenewal_Rates_Transforms
import Definitions.Def_GoldieRenewal_Rates_Model
import Definitions.Def_GoldieRenewal_Rates_Expansion
import Definitions.Def_GoldieRenewal_Implicit_Supplement_LadderLaw

namespace GoldieRenewal.Implicit.Supplement

open MeasureTheory ProbabilityTheory GoldieRenewal.Rates

/-- **Theorem 4.7** (Goldie, *Implicit renewal theory and tails of solutions of random equations*,
Ann. Appl. Probab. 1(1) (1991), p. 138; rate of approach for the random difference equation).
Suppose that `R` solves (1.1) `R =_L Q + MR`, `R` independent of `(M, Q)`, where `M` satisfies (2.3)
`E|M|^κ = 1` for some `κ > 0` and, for some `β ∈ (0, 1)`, (3.3) `E|M|^{κ+β} < ∞` and (3.4) hold and
`E|Q|^{κ+β} < ∞`. Define `η(dx) := e^{κx} P(log M ∈ dx)` if `M ≥ 0` a.s., and otherwise define `η`
by (3.15). Suppose `η` satisfies (3.1) and the subsequent conditions of Theorem 3.1; if
`P(M < 0) > 0`, suppose (3.16) also. Then if `M ≥ 0` a.s., both (3.8) and (3.10) hold, while
otherwise (3.17) holds and `t^κ P(R < −t)` satisfies the same formula.

**Formalization Note** "`R` solves (1.1)" is: `R` independent of `(Q, M)` and the published law
operator `GoldieRenewal.Kesten.rdeOperator` of the law of `(Q, M)` fixes the law of `R`. The two
cases are stated separately, each with its own `η` and the hypotheses that the theorem attaches to
it (`StoneConditions` for `η`; (3.16) only when `P(M < 0) > 0`). (3.8), (3.10) are the published
`ExpansionPos`, `ExpansionNeg`; (3.17) and "the same formula" for the lower tail are
`ExpansionSignedPos`, `ExpansionSignedNeg` (the formula for `−R`, as in Theorem 3.3). Moments are
lower Lebesgue integrals. -/
theorem theorem_4_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Q M R : Ω → ℝ) (hQ : Measurable Q) (hM : Measurable M) (hR : Measurable R)
    (h_indep : IndepFun R (fun ω => (Q ω, M ω)) P)
    (h_fix : GoldieRenewal.Kesten.rdeOperator (P.map (fun ω => (Q ω, M ω))) (P.map R) = P.map R)
    (κ β : ℝ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (h_2_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ κ) ∂P = 1)
    (h_3_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ (κ + β)) ∂P < ⊤)
    (h_3_4 : SpreadOut (logLawGivenNonzero P M))
    (hQ_mom : ∫⁻ ω, ENNReal.ofReal (|Q ω| ^ (κ + β)) ∂P < ⊤) :
    (P {ω | M ω < 0} = 0 → StoneConditions (tiltedLaw P M κ) β →
      ExpansionPos P M R κ β ∧ ExpansionNeg P M R κ β) ∧
    (0 < P {ω | M ω < 0} →
      ∫⁻ ω in {ω | 0 < M ω}, ENNReal.ofReal (M ω ^ (κ + β)) ∂P < 1 →
      StoneConditions (ladderLaw P M κ) β →
      ExpansionSignedPos P M R κ β ∧ ExpansionSignedNeg P M R κ β) := by sorry

end GoldieRenewal.Implicit.Supplement
