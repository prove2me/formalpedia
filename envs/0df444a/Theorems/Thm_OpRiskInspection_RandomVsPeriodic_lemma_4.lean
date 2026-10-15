-- Prove2me | Theorems.Thm_OpRiskInspection_RandomVsPeriodic_lemma_4
-- name    : OpRiskInspection.RandomVsPeriodic.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:32:36.094152+00:00
-- url     : https://prove2.me/theorems/78b85729-496b-4d2a-a5af-fd62955390fc
-- title:
--   Lemma 4, p. 13 — optimal effort under periodic inspection
-- statement:
--   Under periodic inspection at frequency $v>0$, if $P>c/\lambda$, there is an optimal admissible path $a_D^*$ such that, for $0\le t\le1/v$,
--   $$e^{-a_D^*(t)}=\min\left\{\frac{c}{P\lambda}e^{r(1/v-t)},1\right\}.$$
--   Every optimal path agrees with it almost everywhere during that cycle. The canonical optimal path has $a_D^*(1/v)>a_D^*(0)$, and $a_D^*(0)>0$ exactly when $v>\underline v_D=r/\log(P\lambda/c)$. If $0\le P\le c/\lambda$, the zero path is optimal and all optimal paths vanish almost everywhere in the cycle.
--
--   The result describes how effort rises as a known inspection time approaches.
--
--   **Formalization Note** The payoff only observes the path on $[0,1/v]$, and arbitrary optimal paths may differ at its endpoints. Endpoint claims are made about the selected canonical path. The formula with $P$ in the denominator is guarded by $P>c/\lambda$.
-- source:
--   Kim & Xu, Operational Risk Management: Optimal Inspection Policy, SSRN 3491006 (version of July 2023), p. 13, Lemma 4, (13)–(14)

import Mathlib
import Definitions.Def_OpRiskInspection_RandomVsPeriodic_ClosedForms

namespace OpRiskInspection.RandomVsPeriodic

/-- Lemma 4, p. 13: periodic-inspection effort, (13) and (14). -/
theorem lemma_4 (p : Params) (hp : Standing p) :
    (∀ (v P : ℝ), 0 < v → p.c / p.lam < P →
      ∃ a₀ : Effort,
        AgentOptimal p (periodicLaw v) P a₀ ∧
        (∀ t ∈ Set.Icc (0 : ℝ) (1 / v),
          Real.exp (-(a₀ t)) =
            min ((p.c / (P * p.lam)) *
              Real.exp (p.r * (1 / v - t))) 1) ∧
        (∀ a, AgentOptimal p (periodicLaw v) P a →
          ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (1 / v))),
            a t = a₀ t) ∧
        a₀ (0 : ℝ) < a₀ (1 / v) ∧
        (0 < a₀ 0 ↔ vD p P < v)) ∧
    (∀ (v P : ℝ), 0 < v → 0 ≤ P → P ≤ p.c / p.lam →
      AgentOptimal p (periodicLaw v) P (fun _ => 0) ∧
      ∀ a, AgentOptimal p (periodicLaw v) P a →
        ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (1 / v))),
          a t = 0) := by sorry

end OpRiskInspection.RandomVsPeriodic
