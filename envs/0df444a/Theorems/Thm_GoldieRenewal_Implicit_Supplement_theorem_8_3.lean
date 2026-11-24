-- Prove2me | Theorems.Thm_GoldieRenewal_Implicit_Supplement_theorem_8_3
-- name    : GoldieRenewal.Implicit.Supplement.theorem_8_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:18:45.810316+00:00
-- url     : https://prove2.me/theorems/a23996df-7f61-4710-b443-9fda2cbeeccd
-- title:
--   Theorem 8.3 (corrected: exponent −iθ log t) — rate of approach for S =_L MS + N√S + Q: (3.8) with S in place of R
-- statement:
--   Suppose $S$ solves (8.1), $S\overset{L}{=}MS+N\sqrt S+Q$ with $S$ independent of $(Q,N,M)$, where $M\ge0$, $N\ge0$, $Q>0$ a.s. and (8.3) holds. Suppose that $M$ satisfies (2.3) $E|M|^\kappa=1$ for some $\kappa>0$ and that there is $\beta$ with $0<\beta<\min(1,\kappa)$ such that (3.3) $E|M|^{\kappa+\beta}<\infty$ and (3.4) hold and
--   $$
--   EN^{\kappa+\beta}<\infty,\qquad EQ^{\kappa+\beta}<\infty.
--   $$
--   Suppose $\eta(dx):=e^{\kappa x}P(\log M\in dx)$ satisfies (3.1) and the subsequent conditions of Theorem 3.1. Then, with $S$ replacing $R$ in both (3.5) and (3.8), formula (3.8) holds:
--   $$
--   t^\kappa P(S>t)=C_+-\frac1{2\pi}\Re\oint_{\mathcal C}e^{-i\theta\log t}\frac{\hat g_1(\theta)}{1-\hat\eta(\theta)}\,d\theta+O(t^{-\beta/2}),\qquad t\to\infty,
--   $$
--   for every admissible contour $\mathcal C$, where now $g_1(t)=e^{\kappa t}(P(S>e^t)-P(MS>e^t))$.
--
--   This is the rate companion of Theorem 8.2.
--
--   **Formalization Note** "$S$ solves (8.1)" is: $S\ge0$ a.s., $S$ independent of $(Q,N,M)$, and the law operator of (8.1) fixes the law of $S$. (8.3) is encoded as in Proposition 8.1. (3.8) for $S$ is the published `ExpansionPos` applied to $S$. Only the upper tail is claimed, as printed.
--
--   Differences from the source:
--
--   - correction: (3.8) carries e^{−iθt} → the exponent is e^{−iθ log t}; reason: the proof of Theorem 3.2 (pp. 154–155) establishes the remainder in the logarithmic variable; the published (3.8) is stated this way
--   - reading: S solves (8.1) → also S ≥ 0 a.s.; reason: (8.1) contains √S and §8 studies S = R² with R ≥ 0 (p. 142); Proposition 8.1 speaks of laws on [0, ∞)
--   - reading: 𝒞 as in Theorem 3.1 → every admissible axis-parallel rectangle; reason: the convention of the published Theorem 3.1; the contour integral does not depend on the enclosing contour
--   - encoding: independence of S from (Q, N, M); (8.3) with Q′ an independent copy; moments → IndepFun of S and (Q, N, M) plus the law operator of (8.1); (8.3) for the image of law(Q, N, M) ⊗ law(Q) in EReal; lower Lebesgue integrals; reason: as in Proposition 8.1; no instance changes
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 142, Theorem 8.3; proof p. 163

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_CramerConditions
import Definitions.Def_GoldieRenewal_Rates_Transforms
import Definitions.Def_GoldieRenewal_Rates_Model
import Definitions.Def_GoldieRenewal_Rates_Expansion
import Definitions.Def_GoldieRenewal_Implicit_Supplement_Models

namespace GoldieRenewal.Implicit.Supplement

open MeasureTheory ProbabilityTheory GoldieRenewal.Rates

/-- **Theorem 8.3** (Goldie, *Implicit renewal theory and tails of solutions of random equations*,
Ann. Appl. Probab. 1(1) (1991), p. 142; rate of approach for the random polynomial equation).
Suppose `S` solves (8.1) `S =_L MS + N√S + Q`, `S` independent of `(Q, N, M)`, where `M ≥ 0`,
`N ≥ 0`, `Q > 0` a.s. and (8.3) holds. Suppose `M` satisfies (2.3) `E|M|^κ = 1` for some `κ > 0`
and that there is `β > 0` with `β < min(1, κ)` such that (3.3) and (3.4) hold and
`EN^{κ+β} < ∞`, `EQ^{κ+β} < ∞`. Suppose `η(dx) := e^{κx} P(log M ∈ dx)` satisfies (3.1) and the
subsequent conditions of Theorem 3.1. Then, with `S` replacing `R` in both (3.5) and (3.8), formula
(3.8) holds.

**Formalization Note** "`S` solves (8.1)" is: `S ≥ 0` a.s. (the equation contains `√S`, and §8
studies `S = R² ≥ 0`, p. 142), `S` independent of `(Q, N, M)`, and `polyOperator` of the law of
`(Q, N, M)` fixes the law of `S`. (8.3) is encoded as in Proposition 8.1 (`coeffLaw83` of the law
of `(Q, N, M)`, in `EReal`). (3.8) with `S` for `R` is the published `ExpansionPos P M S κ β`
(exponent `−iθ log t`); only the upper tail is claimed. Moments are lower Lebesgue integrals. -/
theorem theorem_8_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Q N M S : Ω → ℝ) (hQ : Measurable Q) (hN : Measurable N) (hM : Measurable M)
    (hS : Measurable S) (hS_nonneg : ∀ᵐ ω ∂P, 0 ≤ S ω)
    (h_indep : IndepFun S (fun ω => (Q ω, N ω, M ω)) P)
    (h_fix : polyOperator (P.map (fun ω => (Q ω, N ω, M ω))) (P.map S) = P.map S)
    (hM_nonneg : ∀ᵐ ω ∂P, 0 ≤ M ω) (hN_nonneg : ∀ᵐ ω ∂P, 0 ≤ N ω)
    (hQ_pos : ∀ᵐ ω ∂P, 0 < Q ω)
    (h_8_3_plus : GoldieRenewal.Implicit.logPlusMoment
      (coeffLaw83 (P.map (fun ω => (Q ω, N ω, M ω)))) < ⊤)
    (h_8_3 : GoldieRenewal.Implicit.logAbsMean
      (coeffLaw83 (P.map (fun ω => (Q ω, N ω, M ω)))) < 0)
    (κ β : ℝ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < min 1 κ)
    (h_2_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ κ) ∂P = 1)
    (h_3_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ (κ + β)) ∂P < ⊤)
    (h_3_4 : SpreadOut (logLawGivenNonzero P M))
    (hN_mom : ∫⁻ ω, ENNReal.ofReal (|N ω| ^ (κ + β)) ∂P < ⊤)
    (hQ_mom : ∫⁻ ω, ENNReal.ofReal (|Q ω| ^ (κ + β)) ∂P < ⊤)
    (h_stone : StoneConditions (tiltedLaw P M κ) β) :
    ExpansionPos P M S κ β := by sorry

end GoldieRenewal.Implicit.Supplement
