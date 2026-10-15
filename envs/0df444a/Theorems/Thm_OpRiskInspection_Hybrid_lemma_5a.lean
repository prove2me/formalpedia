-- Prove2me | Theorems.Thm_OpRiskInspection_Hybrid_lemma_5a
-- name    : OpRiskInspection.Hybrid.lemma_5a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:35:21.568981+00:00
-- url     : https://prove2.me/theorems/c7484bef-ecb3-4635-88ae-09d5ba771603
-- title:
--   Lemma 5(a), pp. 19–20 — the agent's optimal effort under the hybrid policy $H(q)$
-- statement:
--   Under the hybrid policy $H(q)$ with $q\in[0,1]$, frequency $v>0$ and penalty $P$ (inspection at $q/v$ with probability $q$, otherwise at $q/v$ plus an $\mathrm{Exp}(v)$ time):
--
--   1. If $P>c/\lambda$ and $a$ is the effort path with
--   $$
--   e^{-a_t}=\begin{cases}\min\Big\{\dfrac{c}{P\lambda}\Big(\dfrac{r+v}{qr+v}\Big)e^{r(q/v-t)},\,1\Big\} & t\le q/v,\\[2mm] \min\Big\{\dfrac{c}{P\lambda}\Big(\dfrac{r+v}{v}\Big),\,1\Big\} & t>q/v,\end{cases}
--   $$
--   then $a$ is an optimal effort for the agent, and every optimal effort path agrees with $a$ almost everywhere on $(0,\infty)$ when $q<1$, and almost everywhere on $(0,1/v)$ when $q=1$.
--   2. If $P\le c/\lambda$, the zero effort path is optimal and every optimal effort path vanishes almost everywhere on the same set.
--
--   The hybrid effort has a dynamic phase before $q/v$ and a constant phase after it.
--
--   **Formalization Note** Display (22) divides by $P$ and is stated under $P>c/\lambda$; the case $P\le c/\lambda$ is the lemma's "Conversely" clause. Uniqueness is claimed only where the interval can still be running: for $q=1$ the law is a Dirac mass at $1/v$ and effort after $1/v$ never matters. Part (b) of Lemma 5 is not formalized here.
-- source:
--   Kim & Xu, Operational Risk Management: Optimal Inspection Policy, SSRN 3491006 (version of July 2023), pp. 19–20, Lemma 5(a), (22), and the final 'Conversely' clause

import Mathlib
import Definitions.Def_OpRiskInspection_RandomVsPeriodic_Setting

namespace OpRiskInspection.Hybrid

theorem lemma_5a (p : OpRiskInspection.RandomVsPeriodic.Params) (hp : OpRiskInspection.RandomVsPeriodic.Standing p) (q v P : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hv : 0 < v) :
    (p.c / p.lam < P →
      ∀ a : OpRiskInspection.RandomVsPeriodic.Effort,
        (∀ t, t ≤ q / v → Real.exp (-(a t)) =
          min (p.c / (P * p.lam) * ((p.r + v) / (q * p.r + v)) *
            Real.exp (p.r * (q / v - t))) 1) →
        (∀ t, q / v < t → Real.exp (-(a t)) =
          min (p.c / (P * p.lam) * ((p.r + v) / v)) 1) →
        OpRiskInspection.RandomVsPeriodic.AgentOptimal p (OpRiskInspection.RandomVsPeriodic.hybridLaw q v) P a ∧
        ∀ a' : OpRiskInspection.RandomVsPeriodic.Effort, OpRiskInspection.RandomVsPeriodic.AgentOptimal p (OpRiskInspection.RandomVsPeriodic.hybridLaw q v) P a' →
          ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
            (q < 1 ∨ t < q / v) → a' t = a t) ∧
    (P ≤ p.c / p.lam →
        OpRiskInspection.RandomVsPeriodic.AgentOptimal p (OpRiskInspection.RandomVsPeriodic.hybridLaw q v) P (fun _ => 0) ∧
        ∀ a' : OpRiskInspection.RandomVsPeriodic.Effort, OpRiskInspection.RandomVsPeriodic.AgentOptimal p (OpRiskInspection.RandomVsPeriodic.hybridLaw q v) P a' →
          ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
            (q < 1 ∨ t < q / v) → a' t = 0) := by sorry

end OpRiskInspection.Hybrid
