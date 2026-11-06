-- Prove2me | Theorems.Thm_GoldieRenewal_Rates_theorem_3_2_i
-- name    : GoldieRenewal.Rates.theorem_3_2_i
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-06T03:38:47.89169+00:00
-- url     : https://prove2.me/theorems/1b5dd22c-15e0-48f4-8838-15ee877f6957
-- title:
--   Theorem 3.2(i) — upper tail: t^κP(R > t) = C₊ − (1/2π)ℜ∮ e^{−iθ log t} ĝ₁(θ)/(1 − η̂(θ)) dθ + O(t^{−β/2})
-- statement:
--   Let $(\Omega,\mathcal A,P)$ be a probability space, $\kappa>0$, $\beta>0$, and let $M\ge0$ and $R$ be independent real random variables with
--   $$\mathbf E M^\kappa=1\ \ (2.3),\qquad \mathbf E M^{\kappa+\beta}<\infty\ \ (3.3),$$
--   and (3.4): the conditional law of $\log M$ given $M\neq0$ is spread out. Let $\eta(dx)=e^{\kappa x}P(\log M\in dx)$ be the tilted law, and suppose that $\eta$ satisfies the decomposition (3.1) and the subsequent conditions of Theorem 3.1 at this $\beta$. Let $g_1(t)=e^{\kappa t}\big(P(R>e^t)-P(MR>e^t)\big)$ (3.5), let $C_+$ be the constant (2.12), and let $\mathscr C$ be any admissible rectangle contour in the strip $D=\{-\beta<\Im\theta<0\}$ enclosing all zeros of $1-\hat\eta$ in $D$. If
--   $$\int_0^\infty\big|P(R>t)-P(MR>t)\big|\,t^{\kappa+\beta-1}\,dt<\infty\qquad(3.7),$$
--   then, as $t\to\infty$,
--   $$t^\kappa P(R>t)=C_+-\frac1{2\pi}\Re\oint_{\mathscr C}e^{-i\theta\log t}\,\frac{\hat g_1(\theta)}{1-\hat\eta(\theta)}\,d\theta+O(t^{-\beta/2})\qquad(3.8).$$
--
--   This is part (i) of Goldie's Theorem 3.2, the rate-of-approach refinement of the implicit renewal theorem for the upper tail: the second-order term of $t^\kappa P(R>t)-C_+$ is an explicit contour integral determined by the zeros of $1-\hat\eta$ in the strip, up to an error $O(t^{-\beta/2})$.
--
--   **Formalization Note** Same conventions as `GoldieRenewal.Rates.theorem_3_2`: (3.7) is printed with $P(R>-t)$ and is read with $P(R>t)$; integrability on $(0,\infty)$ is `IntegrableOn`; the expansion is stated with the exponent $-i\theta\log t$ that the proof establishes (`ExpansionPos`); moments are lower Lebesgue integrals; $M\ge0$ almost surely.
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 132, Theorem 3.2(i), (3.3)–(3.8)

import Mathlib
import Definitions.Def_GoldieRenewal_Rates_Transforms
import Definitions.Def_GoldieRenewal_Rates_Model
import Definitions.Def_GoldieRenewal_Rates_Expansion

open MeasureTheory ProbabilityTheory

namespace GoldieRenewal.Rates

/-- **Theorem 3.2(i)** (Goldie 1991, p. 132; rate of approach in the implicit renewal theorem,
upper tail, `M ≥ 0`). Let `M ≥ 0` be independent of `R` with (2.3) `E|M|^κ = 1`, (3.3)
`E|M|^{κ+β} < ∞` for some `β > 0`, and (3.4) the conditional law of `log|M|` given `M ≠ 0`
spread out. Suppose `η(dx) := e^{κx}P(log M ∈ dx)` satisfies (3.1) and the subsequent
conditions of Theorem 3.1 (`StoneConditions η β`). Then (3.7)
`∫₀^∞ |P(R > t) − P(MR > t)| t^{κ+β−1} dt < ∞` implies (3.8):
for every admissible rectangle contour `𝒞`,
`t^κ P(R > t) = C₊ − (1/2π) ℜ ∮_𝒞 e^{−iθ log t} ĝ₁(θ)/(1 − η̂(θ)) dθ + O(t^{−β/2})`.
Formalization Note: this is part (i) of `GoldieRenewal.Rates.theorem_3_2`, with the same
conventions: (3.7) is read with `P(R > t)`; "`∫₀^∞ |h(t)| t^{κ+β−1} dt < ∞`" is
`IntegrableOn (h · t^{κ+β−1}) (0, ∞)`; (3.8) is `ExpansionPos` (exponent `−iθ log t`). -/
theorem theorem_3_2_i {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M R : Ω → ℝ) (hM : Measurable M) (hR : Measurable R) (hM_nonneg : ∀ᵐ ω ∂P, 0 ≤ M ω)
    (h_indep : IndepFun R M P) (κ β : ℝ) (hκ : 0 < κ) (hβ : 0 < β)
    (h_2_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ κ) ∂P = 1)
    (h_3_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ (κ + β)) ∂P < ⊤)
    (h_3_4 : SpreadOut (logLawGivenNonzero P M))
    (h_stone : StoneConditions (tiltedLaw P M κ) β)
    (h_3_7 : IntegrableOn (fun t : ℝ =>
        (P.real {ω | t < R ω} - P.real {ω | t < M ω * R ω}) * t ^ (κ + β - 1)) (Set.Ioi 0)) :
    ExpansionPos P M R κ β := by sorry

end GoldieRenewal.Rates
