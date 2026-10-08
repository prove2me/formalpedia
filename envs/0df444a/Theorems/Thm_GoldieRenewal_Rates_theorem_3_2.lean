-- Prove2me | Theorems.Thm_GoldieRenewal_Rates_theorem_3_2
-- name    : GoldieRenewal.Rates.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:14:41.267249+00:00
-- url     : https://prove2.me/theorems/378993c0-f32d-42c6-8c53-b709dc45f143
-- title:
--   Theorem 3.2 — rate of approach: t^κP(R > t) = C₊ − (1/2π)ℜ∮ e^{−iθ log t} ĝ₁(θ)/(1 − η̂(θ)) dθ + O(t^{−β/2})
-- statement:
--   Let $(\Omega,\mathcal A,P)$ be a probability space, $\kappa>0$, $\beta>0$, and let $M\ge0$ and $R$ be independent real random variables with
--   $$\mathbf E M^\kappa=1\ \ (2.3),\qquad \mathbf E M^{\kappa+\beta}<\infty\ \ (3.3),$$
--   and (3.4): the conditional law of $\log M$ given $M\neq0$ is spread out. Then the tilted law $\eta(dx)=e^{\kappa x}P(\log M\in dx)$ is a spread-out probability measure. Suppose further that $\eta$ satisfies (3.1) and the subsequent conditions of Theorem 3.1 at this $\beta$. With $g_{\pm1}$, $C_\pm$ as in (3.5), (3.6), (2.12), (2.13) and $\mathscr C$ any admissible rectangle contour:
--
--   1. If $\int_0^\infty|P(R>t)-P(MR>t)|\,t^{\kappa+\beta-1}\,dt<\infty$ (3.7), then
--   $$t^\kappa P(R>t)=C_+-\frac1{2\pi}\Re\oint_{\mathscr C}e^{-i\theta\log t}\frac{\hat g_1(\theta)}{1-\hat\eta(\theta)}\,d\theta+O(t^{-\beta/2}),\qquad t\to\infty .$$
--   2. If $\int_0^\infty|P(R<-t)-P(MR<-t)|\,t^{\kappa+\beta-1}\,dt<\infty$ (3.9), then
--   $$t^\kappa P(R<-t)=C_--\frac1{2\pi}\Re\oint_{\mathscr C}e^{-i\theta\log t}\frac{\hat g_{-1}(\theta)}{1-\hat\eta(\theta)}\,d\theta+O(t^{-\beta/2}),\qquad t\to\infty .$$
--   3. If $R\overset{\mathcal L}{=}\Psi(R)$ for a jointly measurable random function $\Psi$ and $R$ is independent of $(M,\Psi)$, then (3.7) and (3.9) may be replaced by
--   $$\mathbf E\big|(\Psi(R)^+)^{\kappa+\beta}-((MR)^+)^{\kappa+\beta}\big|<\infty,\qquad \mathbf E\big|(\Psi(R)^-)^{\kappa+\beta}-((MR)^-)^{\kappa+\beta}\big|<\infty .$$
--
--   The theorem quantifies the convergence $t^\kappa P(R>t)\to C_+$ of the implicit renewal theorem: the second-order behaviour is an explicit finite combination of terms $(\log t)^{j-1}t^{\Im\theta_l}$ times oscillating factors, one for each zero $\theta_l$ of $1-\hat\eta$ in the strip.
--
--   **Formalization Note** (3.7) is printed with $P(R>-t)$; it is read with $P(R>t)$ (compare (3.9), (3.11) and the proof). The printed expansions carry $e^{-i\theta t}$; the proof establishes them in the variable $s=\log t$, so they are stated with $e^{-i\theta\log t}$ (see the definition `Expansion`). The contour is any admissible rectangle boundary. Moments are lower Lebesgue integrals; $M\ge0$ almost surely; independence of $R$ from $(M,\Psi)$ is independence of $R$ and $\omega\mapsto(M(\omega),\Psi(\cdot,\omega))$.
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, pp. 132–133, Theorem 3.2, (3.3)–(3.12)

import Mathlib
import Definitions.Def_GoldieRenewal_Rates_Transforms
import Definitions.Def_GoldieRenewal_Rates_Model
import Definitions.Def_GoldieRenewal_Rates_Expansion

open MeasureTheory ProbabilityTheory

namespace GoldieRenewal.Rates

/-- **Theorem 3.2** (Goldie 1991, pp. 132–133; rate of approach in the implicit renewal theorem,
`M ≥ 0`). Let `M ≥ 0` be independent of `R` with (2.3) `E|M|^κ = 1`, (3.3)
`E|M|^{κ+β} < ∞` for some `β > 0`, and (3.4) the conditional law of `log|M|` given `M ≠ 0`
spread out. Then `η(dx) := e^{κx}P(log M ∈ dx)` is a spread-out probability measure. If `η`
satisfies (3.1) and the subsequent conditions of Theorem 3.1 (`StoneConditions η β`), then
(i) (3.7) `∫₀^∞ |P(R > t) − P(MR > t)| t^{κ+β−1} dt < ∞` implies (3.8) (`ExpansionPos`);
(ii) (3.9) `∫₀^∞ |P(R < −t) − P(MR < −t)| t^{κ+β−1} dt < ∞` implies (3.10) (`ExpansionNeg`);
(iii) if `R` satisfies (2.1) `R =_L Ψ(R)` and is independent of `(M, Ψ)`, (3.7) and (3.9) may
be replaced by (3.11) `E|(Ψ(R)⁺)^{κ+β} − ((MR)⁺)^{κ+β}| < ∞` and (3.12)
`E|(Ψ(R)⁻)^{κ+β} − ((MR)⁻)^{κ+β}| < ∞`.
Formalization Note: (3.7) is printed with `P(R > −t)`; it is read `P(R > t)` (compare (3.9),
(3.11), and "(3.7) gives `e^{βt}g₁(t) ∈ L¹(ℝ)`", p. 153). "`∫₀^∞ |h(t)| t^{κ+β−1} dt < ∞`" is
`IntegrableOn (h · t^{κ+β−1}) (0, ∞)`. (3.8)/(3.10) are stated in the form the proof
establishes (exponent `−iθ log t`), see `contourTermPos`. Moments are lower Lebesgue integrals
in `[0, ∞]`. `Ψ : ℝ → Ω → ℝ` is jointly measurable; independence of `R` from `(M, Ψ)` is
independence of `R` and `ω ↦ (M ω, (t ↦ Ψ t ω))` (product σ-algebra on `ℝ × (ℝ → ℝ)`). -/
theorem theorem_3_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M R : Ω → ℝ) (hM : Measurable M) (hR : Measurable R) (hM_nonneg : ∀ᵐ ω ∂P, 0 ≤ M ω)
    (h_indep : IndepFun R M P) (κ β : ℝ) (hκ : 0 < κ) (hβ : 0 < β)
    (h_2_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ κ) ∂P = 1)
    (h_3_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ (κ + β)) ∂P < ⊤)
    (h_3_4 : SpreadOut (logLawGivenNonzero P M)) :
    (IsProbabilityMeasure (tiltedLaw P M κ) ∧ SpreadOut (tiltedLaw P M κ)) ∧
    (StoneConditions (tiltedLaw P M κ) β →
      -- (i)
      (IntegrableOn (fun t : ℝ =>
          (P.real {ω | t < R ω} - P.real {ω | t < M ω * R ω}) * t ^ (κ + β - 1))
          (Set.Ioi 0) → ExpansionPos P M R κ β) ∧
      -- (ii)
      (IntegrableOn (fun t : ℝ =>
          (P.real {ω | R ω < -t} - P.real {ω | M ω * R ω < -t}) * t ^ (κ + β - 1))
          (Set.Ioi 0) → ExpansionNeg P M R κ β) ∧
      -- (iii)
      (∀ Ψ : ℝ → Ω → ℝ, Measurable (Function.uncurry Ψ) →
        P.map (fun ω => Ψ (R ω) ω) = P.map R →
        IndepFun R (fun ω => (M ω, fun t => Ψ t ω)) P →
        (∫⁻ ω, ENNReal.ofReal
            |max (Ψ (R ω) ω) 0 ^ (κ + β) - max (M ω * R ω) 0 ^ (κ + β)| ∂P < ⊤ →
          ExpansionPos P M R κ β) ∧
        (∫⁻ ω, ENNReal.ofReal
            |max (-Ψ (R ω) ω) 0 ^ (κ + β) - max (-(M ω * R ω)) 0 ^ (κ + β)| ∂P < ⊤ →
          ExpansionNeg P M R κ β))) := by sorry

end GoldieRenewal.Rates
