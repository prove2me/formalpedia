-- Prove2me | Theorems.Thm_GoldieRenewal_Implicit_theorem_2_3
-- name    : GoldieRenewal.Implicit.theorem_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:11:55.703592+00:00
-- url     : https://prove2.me/theorems/a0fedab1-604a-44a4-adc1-4de35a0472d6
-- title:
--   Theorem 2.3 — implicit renewal theorem: t^κ P(R > t) → C₊ and t^κ P(R < −t) → C₋, with C± from (2.12)–(2.14)
-- statement:
--   Let $M$ satisfy the conditions of Lemma 2.2 for some $\kappa>0$ — $E|M|^\kappa=1$, $E|M|^\kappa\log^+|M|<\infty$, and the conditional law of $\log|M|$ given $M\ne0$ is nonarithmetic — and let $R$ be a real random variable independent of $M$. Let $m = E|M|^\kappa\log|M|$.
--
--   **Case 1.** Suppose $M\ge0$ a.s. If
--   $$
--   \text{(2.8)}\quad\int_0^\infty|P(R>t)-P(MR>t)|\,t^{\kappa-1}dt<\infty,
--   \quad\text{respectively}\quad
--   \text{(2.9)}\quad\int_0^\infty|P(R<-t)-P(MR<-t)|\,t^{\kappa-1}dt<\infty,
--   $$
--   then
--   $$
--   \text{(2.10)}\quad P(R>t)\sim C_+t^{-\kappa},\qquad\text{respectively}\qquad\text{(2.11)}\quad P(R<-t)\sim C_-t^{-\kappa},\qquad t\to\infty,
--   $$
--   where
--   $$
--   C_+ = \frac1m\int_0^\infty\bigl(P(R>t)-P(MR>t)\bigr)t^{\kappa-1}dt,\qquad
--   C_- = \frac1m\int_0^\infty\bigl(P(R<-t)-P(MR<-t)\bigr)t^{\kappa-1}dt .
--   $$
--
--   **Case 2.** Suppose $P(M<0)>0$. If both (2.8) and (2.9) hold, then both (2.10) and (2.11) hold, with
--   $$
--   C_+ = C_- = \frac1{2m}\int_0^\infty\bigl(P(|R|>t)-P(|MR|>t)\bigr)t^{\kappa-1}dt .
--   $$
--
--   The implicit renewal theorem reduces power-law tail asymptotics for solutions of random equations $R \overset{d}{=} \Psi(R)$ to the integrability conditions (2.8), (2.9), which compare $R$ with $MR$ rather than solving for the law of $R$. The theorem has content only when $E|R|^\kappa=\infty$: otherwise $C_++C_-=0$.
--
--   **Formalization Note** "$P(R>t)\sim C_+t^{-\kappa}$" is $t^\kappa P(R>t)\to C_+$, which includes $C_+=0$, read as $o(t^{-\kappa})$ as the paper prescribes (p. 130); no positivity of the constants is claimed. No equation for $R$ and no moment of $R$ is assumed. (2.8), (2.9) are integrability on $(0,\infty)$ and the constants are the corresponding Bochner integrals.
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, pp. 129–130, Theorem 2.3

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_CramerConditions
import Definitions.Def_GoldieRenewal_Implicit_TailConstants
open MeasureTheory ProbabilityTheory Filter Topology

namespace GoldieRenewal.Implicit

/-- **Theorem 2.3, the implicit renewal theorem** (Goldie, *Implicit renewal theory and tails of
solutions of random equations*, Ann. Appl. Probab. 1(1):126–166 (1991), pp. 129–130).
Let `M` satisfy the conditions of Lemma 2.2 and let `R` be independent of `M`.

* **Case 1.** Suppose `M ≥ 0` a.s. If (2.8) `∫₀^∞ |P(R > t) − P(MR > t)| t^{κ−1} dt < ∞`, then
  (2.10) `P(R > t) ~ C₊ t^{−κ}` as `t → ∞`, with `C₊` from (2.12); respectively, if (2.9)
  `∫₀^∞ |P(R < −t) − P(MR < −t)| t^{κ−1} dt < ∞`, then (2.11) `P(R < −t) ~ C₋ t^{−κ}`, with `C₋`
  from (2.13).
* **Case 2.** Suppose `P(M < 0) > 0`. If both (2.8) and (2.9) hold, then both (2.10) and (2.11)
  hold with `C₊ = C₋ = (1/(2m)) ∫₀^∞ (P(|R| > t) − P(|MR| > t)) t^{κ−1} dt` (2.14).

**Formalization Note** "`P(R > t) ~ C₊ t^{−κ}`" is `t^κ P(R > t) → C₊`; this includes `C₊ = 0`, read
as `o(t^{−κ})` as the paper prescribes (p. 130). The constants are `Cplus`, `Cminus`, `Ctwo`, with
`m = E|M|^κ log|M|` the constant (2.7) of the law of `M`. (2.8), (2.9) are `TailCondPlus`,
`TailCondMinus` (integrability on `(0, ∞)`). No equation is assumed for `R` and no moment of `R`. -/
theorem theorem_2_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M R : Ω → ℝ) (hM : Measurable M) (hR : Measurable R) (κ : ℝ)
    (hC : CramerConditions κ (P.map M)) (hind : IndepFun R M P) :
    ((∀ᵐ ω ∂P, 0 ≤ M ω) →
        (TailCondPlus P M R κ →
          Tendsto (fun t : ℝ => t ^ κ * P.real {ω | t < R ω}) atTop (𝓝 (Cplus P M R κ))) ∧
        (TailCondMinus P M R κ →
          Tendsto (fun t : ℝ => t ^ κ * P.real {ω | R ω < -t}) atTop (𝓝 (Cminus P M R κ)))) ∧
      (0 < P {ω | M ω < 0} → TailCondPlus P M R κ → TailCondMinus P M R κ →
        Tendsto (fun t : ℝ => t ^ κ * P.real {ω | t < R ω}) atTop (𝓝 (Ctwo P M R κ)) ∧
          Tendsto (fun t : ℝ => t ^ κ * P.real {ω | R ω < -t}) atTop (𝓝 (Ctwo P M R κ))) := by sorry

end GoldieRenewal.Implicit
