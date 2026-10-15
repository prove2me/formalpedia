-- Prove2me | Theorems.Thm_OpRiskInspection_RandomVsPeriodic_lemma_3
-- name    : OpRiskInspection.RandomVsPeriodic.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:32:31.612045+00:00
-- url     : https://prove2.me/theorems/e470b50e-1aab-4bc8-926a-e1b4d5398b88
-- title:
--   Lemma 3, p. 13 — optimal effort under random inspection
-- statement:
--   Under random inspection at frequency $v>0$, if $P>c/\lambda$, there is an optimal constant effort $a_R^*\ge0$ satisfying
--   $$e^{-a_R^*}=\min\left\{\frac{c}{P\lambda}\frac{r+v}{v},1\right\},\qquad a_R^*>0\iff v>\underline v_R=\frac{rc}{P\lambda-c}.$$
--   Every optimal admissible effort path agrees with this constant almost everywhere at nonnegative times. If $0\le P\le c/\lambda$, zero effort is optimal, and every optimal path is zero almost everywhere at nonnegative times.
--
--   This identifies the agent's response and the frequency threshold separating effort inducement from error correction.
--
--   **Formalization Note** Equality of general measurable paths is almost everywhere because changing a path on a null set does not affect the payoff. The formula with $P$ in its denominator is stated only when $P>c/\lambda$.
-- source:
--   Kim & Xu, Operational Risk Management: Optimal Inspection Policy, SSRN 3491006 (version of July 2023), p. 13, Lemma 3, (11)–(12)

import Mathlib
import Definitions.Def_OpRiskInspection_RandomVsPeriodic_ClosedForms

namespace OpRiskInspection.RandomVsPeriodic

/-- Lemma 3, p. 13: random-inspection effort, (11) and (12). -/
theorem lemma_3 (p : Params) (hp : Standing p) :
    (∀ (v P : ℝ), 0 < v → p.c / p.lam < P →
      ∃ a₀ : ℝ,
        0 ≤ a₀ ∧
        Real.exp (-a₀) = min ((p.c / (P * p.lam)) * ((p.r + v) / v)) 1 ∧
        AgentOptimal p (randomLaw v) P (fun _ => a₀) ∧
        (∀ a, AgentOptimal p (randomLaw v) P a →
          ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))), a t = a₀) ∧
        (0 < a₀ ↔ vR p P < v)) ∧
    (∀ (v P : ℝ), 0 < v → 0 ≤ P → P ≤ p.c / p.lam →
      AgentOptimal p (randomLaw v) P (fun _ => 0) ∧
      ∀ a, AgentOptimal p (randomLaw v) P a →
        ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))), a t = 0) := by sorry

end OpRiskInspection.RandomVsPeriodic
