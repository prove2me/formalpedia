-- Prove2me | Theorems.Thm_GoldieRenewal_Kesten_corollary_2_4
-- name    : GoldieRenewal.Kesten.corollary_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:09:17.289466+00:00
-- url     : https://prove2.me/theorems/026698f0-b272-4954-b5ed-1d739b5159a4
-- title:
--   Corollary 2.4 — implicit renewal theorem with moment conditions (2.16)–(2.17) and constants (2.18)–(2.20)
-- statement:
--   Let $(\Omega,\mathcal A,P)$ be a probability space, $\Psi:\mathbb R\times\Omega\to\mathbb R$ jointly measurable, and $R$, $M$ real random variables. Suppose $R$ satisfies the random equation (2.1), $\Psi(R)\overset{\mathcal L}{=}R$, that $M$ satisfies the conditions of Lemma 2.2 for some $\kappa>0$ — $\mathbf E|M|^\kappa=1$, $\mathbf E|M|^\kappa\log^+|M|<\infty$, $\log|M|$ given $M\ne0$ nonarithmetic — and that $R$ is independent of $(\Psi,M)$. Let $m=\mathbf E|M|^\kappa\log|M|$.
--
--   1. **Case 1, $M\ge 0$ a.s.** If $\mathbf E\big|(\Psi(R)^+)^\kappa-((MR)^+)^\kappa\big|<\infty$ (2.16), then
--   $$
--   \lim_{t\to\infty} t^\kappa P(R>t) = C_+ := \frac{1}{\kappa m}\,\mathbf E\big((\Psi(R)^+)^\kappa-((MR)^+)^\kappa\big)\qquad\text{(2.18)};
--   $$
--   if $\mathbf E\big|(\Psi(R)^-)^\kappa-((MR)^-)^\kappa\big|<\infty$ (2.17), then $\lim_{t\to\infty}t^\kappa P(R<-t) = C_- := \frac{1}{\kappa m}\mathbf E\big((\Psi(R)^-)^\kappa-((MR)^-)^\kappa\big)$ (2.19).
--   2. **Case 2, $P(M<0)>0$.** If both (2.16) and (2.17) hold, then both limits hold with
--   $$
--   C_+ = C_- = \frac{1}{2\kappa m}\,\mathbf E\big(|\Psi(R)|^\kappa-|MR|^\kappa\big)\qquad\text{(2.20)}.
--   $$
--
--   This is the form of the implicit renewal theorem used for concrete random equations: the integrability conditions of Theorem 2.3 on tail differences are replaced by moment conditions on $\Psi(R)$ and $MR$, which can be checked directly.
--
--   **Formalization Note** "$P(R>t)\sim C_+t^{-\kappa}$" is stated as $t^\kappa P(R>t)\to C_+$, the reading the paper prescribes on p. 130 (it includes $C_+=0$). Independence of $R$ from $(\Psi,M)$ is independence of $R$ from $\omega\mapsto(M(\omega),\Psi(\cdot,\omega))$, with the product σ-algebra on functions $\mathbb R\to\mathbb R$. In (2.16) the printed connective is read as a minus sign.
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 130, Corollary 2.4, (2.16)–(2.20)

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_CramerConditions

namespace GoldieRenewal.Kesten

open MeasureTheory ProbabilityTheory Filter Topology

/-- **Corollary 2.4** (Goldie, *Implicit renewal theory and tails of solutions of random
equations*, Ann. Appl. Probab. 1(1) (1991), p. 130). Let `Ψ : ℝ × Ω → ℝ` be jointly measurable,
let `R` satisfy (2.1) (`Ψ(R) =_L R`), and let `M` satisfy the conditions of Lemma 2.2 with
`R` independent of `(Ψ, M)`. Write `m = E|M|^κ log|M|`.

* Case 1 (`M ≥ 0` a.s.): if (2.16) `E|(Ψ(R)⁺)^κ − ((MR)⁺)^κ| < ∞` then
  `t^κ P(R > t) → C₊ = (κm)⁻¹ E((Ψ(R)⁺)^κ − ((MR)⁺)^κ)` (2.18); if (2.17)
  `E|(Ψ(R)⁻)^κ − ((MR)⁻)^κ| < ∞` then `t^κ P(R < −t) → C₋ = (κm)⁻¹ E((Ψ(R)⁻)^κ − ((MR)⁻)^κ)` (2.19).
* Case 2 (`P(M < 0) > 0`): if both (2.16) and (2.17) hold, both limits hold with
  `C₊ = C₋ = (2κm)⁻¹ E(|Ψ(R)|^κ − |MR|^κ)` (2.20).

**Formalization Note** (2.16) is printed with a glyph resembling "∼" in place of "−"; read "−"
(see (2.17)). "`P(R > t) ~ C₊ t^{−κ}`" is read, as the paper instructs on p. 130 (which covers
`C₊ = 0`), as `t^κ P(R > t) → C₊`. "`R` independent of `(Ψ, M)`" is `IndepFun` of `R` and
`ω ↦ (M ω, (t ↦ Ψ(t, ω)))`, with the product σ-algebra on `ℝ → ℝ`. Conditions (2.16)/(2.17) are
`Integrable` hypotheses, so the expectations in (2.18)–(2.20) are genuine. -/
theorem corollary_2_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (Ψ : ℝ → Ω → ℝ) (hΨ : Measurable (fun p : ℝ × Ω => Ψ p.1 p.2))
    (M R : Ω → ℝ) (hM : Measurable M) (hR : Measurable R)
    (hCramer : GoldieRenewal.Implicit.CramerConditions κ (P.map M))
    (hindep : IndepFun R (fun ω => (M ω, fun t => Ψ t ω)) P)
    (hfix : P.map (fun ω => Ψ (R ω) ω) = P.map R) :
    (P {ω | M ω < 0} = 0 →
      (Integrable (fun ω => (max (Ψ (R ω) ω) 0) ^ κ - (max (M ω * R ω) 0) ^ κ) P →
        Tendsto (fun t : ℝ => t ^ κ * P.real {ω | t < R ω}) atTop
          (𝓝 ((κ * GoldieRenewal.Implicit.cramerMean κ (P.map M))⁻¹ *
            ∫ ω, ((max (Ψ (R ω) ω) 0) ^ κ - (max (M ω * R ω) 0) ^ κ) ∂P))) ∧
      (Integrable (fun ω => (max (-Ψ (R ω) ω) 0) ^ κ - (max (-(M ω * R ω)) 0) ^ κ) P →
        Tendsto (fun t : ℝ => t ^ κ * P.real {ω | R ω < -t}) atTop
          (𝓝 ((κ * GoldieRenewal.Implicit.cramerMean κ (P.map M))⁻¹ *
            ∫ ω, ((max (-Ψ (R ω) ω) 0) ^ κ - (max (-(M ω * R ω)) 0) ^ κ) ∂P)))) ∧
    (0 < P {ω | M ω < 0} →
      Integrable (fun ω => (max (Ψ (R ω) ω) 0) ^ κ - (max (M ω * R ω) 0) ^ κ) P →
      Integrable (fun ω => (max (-Ψ (R ω) ω) 0) ^ κ - (max (-(M ω * R ω)) 0) ^ κ) P →
        Tendsto (fun t : ℝ => t ^ κ * P.real {ω | t < R ω}) atTop
          (𝓝 ((2 * κ * GoldieRenewal.Implicit.cramerMean κ (P.map M))⁻¹ *
            ∫ ω, (|Ψ (R ω) ω| ^ κ - |M ω * R ω| ^ κ) ∂P)) ∧
        Tendsto (fun t : ℝ => t ^ κ * P.real {ω | R ω < -t}) atTop
          (𝓝 ((2 * κ * GoldieRenewal.Implicit.cramerMean κ (P.map M))⁻¹ *
            ∫ ω, (|Ψ (R ω) ω| ^ κ - |M ω * R ω| ^ κ) ∂P))) := by sorry

end GoldieRenewal.Kesten
