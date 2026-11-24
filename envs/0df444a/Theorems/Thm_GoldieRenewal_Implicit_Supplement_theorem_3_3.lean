-- Prove2me | Theorems.Thm_GoldieRenewal_Implicit_Supplement_theorem_3_3
-- name    : GoldieRenewal.Implicit.Supplement.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:13:29.220305+00:00
-- url     : https://prove2.me/theorems/8077bd53-c503-4004-a978-c66cdcfce2fc
-- title:
--   Theorem 3.3 (corrected: exponent −iθ log t, (3.7) with P(R > t)) — rate of approach when P(M < 0) > 0: η of (3.15) spread out, expansion (3.17) for both tails
-- statement:
--   Let $(\Omega,\mathcal A,P)$ be a probability space and $M,R$ independent random variables with $P(M<0)>0$. Let $\kappa>0$ and $\beta>0$, and assume
--
--   1. (2.3) $E|M|^\kappa=1$;
--   2. (3.4) the conditional law of $\log|M|$ given $M\neq0$ is spread out;
--   3. (3.3) $E|M|^{\kappa+\beta}<\infty$;
--   4. (3.16) $E\,M^{\kappa+\beta}\mathbf 1_{M>0}<1$.
--
--   Then the ladder law $\eta$ of (3.15) is spread out. Suppose further that $\eta$ satisfies Stone's decomposition (3.1) and the subsequent conditions of Theorem 3.1. Let $C_+=C_-$ be the constant (2.14), and let $\mu_\pm$, $g_{\pm1}$ be as in the definitions.
--
--   (i) If
--   $$
--   \int_0^\infty|P(R>t)-P(MR>t)|\,t^{\kappa+\beta-1}\,dt<\infty\quad(3.7),\qquad \int_0^\infty|P(R<-t)-P(MR<-t)|\,t^{\kappa+\beta-1}\,dt<\infty\quad(3.9),
--   $$
--   then for every admissible contour $\mathcal C$,
--   $$
--   t^\kappa P(R>t) = C_+ - \frac1{2\pi}\Re\oint_{\mathcal C} e^{-i\theta\log t}\Bigl(\frac{\hat g_1(\theta)+\hat g_{-1}(\theta)}{2(1-\hat\mu_+(\theta)-\hat\mu_-(\theta))}+\frac{\hat g_1(\theta)-\hat g_{-1}(\theta)}{2(1-\hat\mu_+(\theta)+\hat\mu_-(\theta))}\Bigr)d\theta + O(t^{-\beta/2})
--   $$
--   as $t\to\infty$ (3.17), and the same formula holds for $t^\kappa P(R<-t)$, with $-R$ in place of $R$ on the right.
--
--   (ii) If $R\overset{L}{=}\Psi(R)$ with $R$ independent of $(M,\Psi)$ (equation (2.1)), then (3.7) and (3.9) may be replaced by
--   $$
--   E\bigl|(\Psi(R)^+)^{\kappa+\beta}-((MR)^+)^{\kappa+\beta}\bigr|<\infty\quad(3.11),\qquad E\bigl|(\Psi(R)^-)^{\kappa+\beta}-((MR)^-)^{\kappa+\beta}\bigr|<\infty\quad(3.12).
--   $$
--
--   This is the rate companion of Case 2 of the implicit renewal theorem (Theorem 2.3), the case in which $M$ takes negative values with positive probability.
--
--   **Formalization Note** The hypotheses are encoded as in the published `GoldieRenewal.Rates.theorem_3_2`: weighted tail integrals as integrability on $(0,\infty)$, moments as lower Lebesgue integrals, $\Psi$ jointly measurable, and independence of $R$ from $(M,\Psi)$ as independence of $R$ and $\omega\mapsto(M(\omega),\Psi(\cdot,\omega))$. The contour ranges over every admissible rectangle. $\eta$ is not asserted to be a probability measure.
--
--   Differences from the source:
--
--   - correction: (3.17) carries e^{−iθt} in the contour integral → the exponent is e^{−iθ log t}; reason: the proof (pp. 154–156) establishes the remainder in the logarithmic variable s = log t (ℜr₁(s) = O(e^{−βs/2}) with r(s) = e^{κs}P(R > e^s)); the published (3.8) and (3.10) are stated the same way
--   - correction: (3.7) is printed with P(R > −t) → P(R > t); reason: compare (3.9), (3.11) and the proof's use of (3.7) as e^{βt}g₁(t) ∈ L¹; the published Theorem 3.2 reads it the same way
--   - reading: the same formula holds for t^κP(R < −t) → (3.17) for −R, i.e. t^κP(R < −t) on the left and ĝ₁, ĝ₋₁ exchanged on the right; reason: the proof says 'for −R in place of R' (p. 156); P(−R > t) = P(R < −t) and C₊ = C₋
--   - reading: C₊ in (3.17) → the Case 2 constant (2.14), GoldieRenewal.Implicit.Ctwo; reason: the theorem says 'Recall that C₊ = C₋ in this case', which is Case 2 of Theorem 2.3, where both constants are (2.14)
--   - reading: 𝒞 as in Theorem 3.1, a simple closed contour in −β < ℑθ < 0 enclosing all zeroes of 1 − η̂ there → every axis-parallel rectangle in the strip whose interior contains every zero of 1 − η̂ in the strip; reason: the convention of the published Theorem 3.1; by Cauchy's theorem the contour integral is the same for every contour enclosing the same zeros
--   - encoding: moments E|·|, weighted tail integrals ∫₀^∞|·| t^{κ+β−1}dt < ∞, independence of R from (M, Ψ) → lower Lebesgue integrals, IntegrableOn on (0, ∞), IndepFun of R and (M, Ψ(·)); reason: these are the encodings of the published Theorem 3.2; they change no instance
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 134, Theorem 3.3; proof pp. 155–156

import Mathlib
import Definitions.Def_GoldieRenewal_Rates_Transforms
import Definitions.Def_GoldieRenewal_Rates_Model
import Definitions.Def_GoldieRenewal_Implicit_Supplement_LadderLaw

namespace GoldieRenewal.Implicit.Supplement

open MeasureTheory ProbabilityTheory GoldieRenewal.Rates

/-- **Theorem 3.3** (Goldie, *Implicit renewal theory and tails of solutions of random equations*,
Ann. Appl. Probab. 1(1) (1991), p. 134; rate of approach when `M` takes negative values). Suppose
`P(M < 0) > 0`. Let `M` be independent of `R` and satisfy (2.3) `E|M|^κ = 1`, (3.4) the conditional
law of `log|M|` given `M ≠ 0` is spread out, and (3.3) `E|M|^{κ+β} < ∞` for some `β > 0`, with `β`
so small that (3.16) `E M^{κ+β} 1_{M>0} < 1`. Then `η` of (3.15) is spread out. If `η` satisfies
(3.1) and the subsequent conditions of Theorem 3.1 (`StoneConditions η β`), then
(i) if (3.7) `∫₀^∞ |P(R > t) − P(MR > t)| t^{κ+β−1} dt < ∞` and (3.9)
`∫₀^∞ |P(R < −t) − P(MR < −t)| t^{κ+β−1} dt < ∞`, the expansion (3.17) holds for
`t^κ P(R > t)` (`ExpansionSignedPos`), and the same formula holds for `t^κ P(R < −t)`
(`ExpansionSignedNeg`), with `C₊ = C₋` the constant (2.14);
(ii) if `R` satisfies (2.1) and is independent of `(M, Ψ)`, (3.7) and (3.9) may be replaced by
(3.11) `E|(Ψ(R)⁺)^{κ+β} − ((MR)⁺)^{κ+β}| < ∞` and (3.12) `E|(Ψ(R)⁻)^{κ+β} − ((MR)⁻)^{κ+β}| < ∞`.

**Formalization Note** Hypothesis encodings are those of the published
`GoldieRenewal.Rates.theorem_3_2`: (3.7) is printed with `P(R > −t)` and read `P(R > t)`;
"`∫₀^∞ |h(t)| t^{κ+β−1} dt < ∞`" is `IntegrableOn` on `(0, ∞)`; moments are lower Lebesgue integrals;
`Ψ : ℝ → Ω → ℝ` is jointly measurable and independence of `R` from `(M, Ψ)` is `IndepFun` of `R` and
`ω ↦ (M ω, (t ↦ Ψ t ω))`. (3.16) is the lower Lebesgue integral of `M^{κ+β}` over `{M > 0}`. The
contour 𝒞 "as in Theorem 3.1" ranges over every admissible rectangle for `1 − η̂`; (3.17) is stated
with the exponent `−iθ log t` (see `contourTermSigned`). "The same formula for `t^κP(R < −t)`" is
(3.17) for `−R`, as the proof says (p. 156). `η` is not asserted to be a probability measure. -/
theorem theorem_3_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M R : Ω → ℝ) (hM : Measurable M) (hR : Measurable R) (hM_neg : 0 < P {ω | M ω < 0})
    (h_indep : IndepFun R M P) (κ β : ℝ) (hκ : 0 < κ) (hβ : 0 < β)
    (h_2_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ κ) ∂P = 1)
    (h_3_4 : SpreadOut (logLawGivenNonzero P M))
    (h_3_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ (κ + β)) ∂P < ⊤)
    (h_3_16 : ∫⁻ ω in {ω | 0 < M ω}, ENNReal.ofReal (M ω ^ (κ + β)) ∂P < 1) :
    SpreadOut (ladderLaw P M κ) ∧
    (StoneConditions (ladderLaw P M κ) β →
      -- (i)
      (IntegrableOn (fun t : ℝ =>
          (P.real {ω | t < R ω} - P.real {ω | t < M ω * R ω}) * t ^ (κ + β - 1))
          (Set.Ioi 0) →
        IntegrableOn (fun t : ℝ =>
          (P.real {ω | R ω < -t} - P.real {ω | M ω * R ω < -t}) * t ^ (κ + β - 1))
          (Set.Ioi 0) →
        ExpansionSignedPos P M R κ β ∧ ExpansionSignedNeg P M R κ β) ∧
      -- (ii)
      (∀ Ψ : ℝ → Ω → ℝ, Measurable (Function.uncurry Ψ) →
        P.map (fun ω => Ψ (R ω) ω) = P.map R →
        IndepFun R (fun ω => (M ω, fun t => Ψ t ω)) P →
        ∫⁻ ω, ENNReal.ofReal
            |max (Ψ (R ω) ω) 0 ^ (κ + β) - max (M ω * R ω) 0 ^ (κ + β)| ∂P < ⊤ →
        ∫⁻ ω, ENNReal.ofReal
            |max (-Ψ (R ω) ω) 0 ^ (κ + β) - max (-(M ω * R ω)) 0 ^ (κ + β)| ∂P < ⊤ →
        ExpansionSignedPos P M R κ β ∧ ExpansionSignedNeg P M R κ β)) := by sorry

end GoldieRenewal.Implicit.Supplement
