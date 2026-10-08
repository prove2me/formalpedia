-- Prove2me | Theorems.Thm_GoldieRenewal_Implicit_eq_9_15
-- name    : GoldieRenewal.Implicit.eq_9_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:11:39.725975+00:00
-- url     : https://prove2.me/theorems/8520194d-a416-4d42-9fcd-35732b82ca3a
-- title:
--   (9.15), p. 148 — in Case 2a, ř = ğ₁ ∗ ν + ğ₋₁ ∗ η₀ ∗ ν
-- statement:
--   Let $M$ satisfy the conditions of Lemma 2.2 with $P(M>0)>0$ and $P(M<0)>0$ (Case 2a), let $R$ be independent of $M$, and assume (2.8) and (2.9). Let $r, g_1, g_{-1}$ be as in (9.3), (3.5), (3.6), let $\eta$ be the law (9.11), $\nu = \sum_{n\ge0}\eta^{(n)}$ its renewal measure and $\eta_0 = \sum_{n\ge1}qp^{n-1}\eta_-*\eta_+^{(n-1)}$. Then for every $t\in\mathbb R$ both convolutions below converge absolutely and
--   $$
--   \check r(t) = \check g_1*\nu(t) + \check g_{-1}*\eta_0*\nu(t).
--   $$
--
--   Applying the key renewal theorem to each term gives $\check r(t)\to\frac1{2m}\int_{\mathbb R}(g_1+g_{-1})$, which is the constant (2.14).
--
--   **Formalization Note** Only the second (measure-form) equality of (9.15) is stated; the first is in terms of the random walks $W^{(\pm)}$ of the proof. $\check g_{-1}*\eta_0*\nu$ is the convolution of $\check g_{-1}$ with the measure $\eta_0*\nu$.
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, §9, proof of Theorem 2.3, Case 2a, (9.15), p. 148 (η₀ p. 148, ν p. 147)

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_CramerConditions
import Definitions.Def_GoldieRenewal_Implicit_DRi
import Definitions.Def_GoldieRenewal_Implicit_TailConstants
import Definitions.Def_GoldieRenewal_Implicit_RenewalMeasures
open MeasureTheory ProbabilityTheory

namespace GoldieRenewal.Implicit

/-- **(9.15)**, second equality (Goldie 1991, Ann. Appl. Probab. 1(1), §9, proof of Theorem 2.3,
Case 2a, p. 148): `ř(t) = ğ₁ ∗ ν(t) + ğ₋₁ ∗ η₀ ∗ ν(t)`, `t ∈ ℝ`.

Setting: `M` satisfies the conditions of Lemma 2.2, `P(M > 0) > 0`, `P(M < 0) > 0` (Case 2a), `R` is
independent of `M`, and (2.8), (2.9) hold. Here `r(t) := e^{κt} P(R > e^t)` (9.3),
`g₁`, `g₋₁` are (3.5), (3.6), `η` is the law (9.11), `ν := Σ_{n≥0} η^{(n)}` (p. 147) and
`η₀ := Σ_{n≥1} q p^{n−1} η₋ ∗ η₊^{(n−1)}` (p. 148). Both convolutions converge absolutely for every
`t`.

**Formalization Note** Only the second (measure-form) equality of (9.15) is stated; the first one
is in terms of the random walks `W^{(±)}` of the proof. `η`, `η₀` are `etaCase2`, `etaZero`
(defined from the law of `M`); `ğ₋₁ ∗ η₀ ∗ ν` is the convolution of `ğ₋₁` with the measure
`η₀ ∗ ν`. Absolute convergence of both terms is part of the conclusion. -/
theorem eq_9_15 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M R : Ω → ℝ) (hM : Measurable M) (hR : Measurable R) (κ : ℝ)
    (hC : CramerConditions κ (P.map M)) (hind : IndepFun R M P)
    (hpos : 0 < P {ω | 0 < M ω}) (hneg : 0 < P {ω | M ω < 0})
    (h28 : TailCondPlus P M R κ) (h29 : TailCondMinus P M R κ) :
    ∀ t : ℝ,
      Integrable (fun u => smooth (gOne P M R κ) (t - u))
          (renewalMeasure (etaCase2 κ (P.map M))) ∧
        Integrable (fun u => smooth (gNegOne P M R κ) (t - u))
          (etaZero κ (P.map M) ∗ renewalMeasure (etaCase2 κ (P.map M))) ∧
        smooth (rFun P R κ) t =
          convFun (smooth (gOne P M R κ)) (renewalMeasure (etaCase2 κ (P.map M))) t +
            convFun (smooth (gNegOne P M R κ))
              (etaZero κ (P.map M) ∗ renewalMeasure (etaCase2 κ (P.map M))) t := by sorry

end GoldieRenewal.Implicit
