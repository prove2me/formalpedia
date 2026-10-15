-- Prove2me | Theorems.Thm_OpRiskInspection_Hybrid_lemma_3
-- name    : OpRiskInspection.Hybrid.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:35:14.91598+00:00
-- url     : https://prove2.me/theorems/d14e7a55-03f4-4f0e-ba7f-ceb17300d549
-- title:
--   Lemma 3, p. 13 — the agent's optimal effort under the random policy
-- statement:
--   Under the random policy with frequency $v>0$ (inspection intervals $\tau\sim\mathrm{Exp}(v)$) and penalty $P$:
--
--   1. If $P>c/\lambda$ and $a^*$ is the number with
--   $$
--   e^{-a^*}=\min\Big\{\frac{c}{P\lambda}\Big(\frac{r+v}{v}\Big),\,1\Big\},
--   $$
--   then the constant effort path $a_t\equiv a^*$ is an optimal effort for the agent, every optimal effort path equals $a^*$ almost everywhere on $(0,\infty)$, and
--   $$
--   a^*>0\iff v>\underline v_R:=\frac{rc}{P\lambda-c}.
--   $$
--   2. If $P\le c/\lambda$, the zero effort path is optimal and every optimal effort path vanishes almost everywhere on $(0,\infty)$.
--
--   This identifies the effort regime that determines the form of the principal's payoff under the random policy.
--
--   **Formalization Note** Display (11) divides by $P$; it is stated under $P>c/\lambda$, and the case $P\le c/\lambda$ is the lemma's "Conversely" clause. "The optimal effort is" is read as: the given path is optimal and optimal paths are unique up to null sets.
-- source:
--   Kim & Xu, Operational Risk Management: Optimal Inspection Policy, SSRN 3491006 (version of July 2023), p. 13, Lemma 3, (11), (12)

import Mathlib
import Definitions.Def_OpRiskInspection_RandomVsPeriodic_Setting

namespace OpRiskInspection.Hybrid

theorem lemma_3 (p : OpRiskInspection.RandomVsPeriodic.Params) (hp : OpRiskInspection.RandomVsPeriodic.Standing p) (v P : ℝ) (hv : 0 < v) :
    (p.c / p.lam < P →
      ∀ a : ℝ, Real.exp (-a) = min (p.c / (P * p.lam) * ((p.r + v) / v)) 1 →
        OpRiskInspection.RandomVsPeriodic.AgentOptimal p (OpRiskInspection.RandomVsPeriodic.randomLaw v) P (fun _ => a) ∧
        (∀ a' : OpRiskInspection.RandomVsPeriodic.Effort, OpRiskInspection.RandomVsPeriodic.AgentOptimal p (OpRiskInspection.RandomVsPeriodic.randomLaw v) P a' →
          ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))), a' t = a) ∧
        (0 < a ↔ p.r * p.c / (P * p.lam - p.c) < v)) ∧
    (P ≤ p.c / p.lam →
        OpRiskInspection.RandomVsPeriodic.AgentOptimal p (OpRiskInspection.RandomVsPeriodic.randomLaw v) P (fun _ => 0) ∧
        ∀ a' : OpRiskInspection.RandomVsPeriodic.Effort, OpRiskInspection.RandomVsPeriodic.AgentOptimal p (OpRiskInspection.RandomVsPeriodic.randomLaw v) P a' →
          ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))), a' t = 0) := by sorry

end OpRiskInspection.Hybrid
