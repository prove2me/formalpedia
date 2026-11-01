-- Prove2me | Theorems.Thm_GreedyReusableNet_lemma_1
-- name    : GreedyReusableNet.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:38:14.966866+00:00
-- url     : https://prove2.me/theorems/1d30c6b1-7f3e-4f9a-801d-958b11afdf05
-- title:
--   Lemma 1 — the queue coupling feeds OPT i.i.d. uniform seeds
-- statement:
--   Let $\pi$ and OPT be admissible policies run in the queue coupling.
--
--   1. For every period $t<T$ and arm $i$, on the event that OPT activates $i$ at $t$, the seed OPT uses for the blocking time of $i$ is uniform on $[0,1]$ and independent of everything OPT has observed before that draw (its history, its action set and its activated bundles at $t$) and of all seeds OPT used in earlier periods. Formally, for every value $x$ of OPT's observations, every measurable set $E$ of earlier seeds and every Borel set $U$,
--   $$\Pr[\text{obs}=x,\ \text{past seeds}\in E,\ i\text{ activated},\ \text{seed}\in U]=\Pr[\text{obs}=x,\ \text{past seeds}\in E,\ i\text{ activated}]\cdot\mathrm{Leb}(U\cap[0,1]).$$
--   2. Consequently OPT's history in the coupled run has the same law as in its own run.
--
--   This is Lemma 1 of Simchi-Levi, Zheng and Zhu: "For any arm $i\in[N]$, the samples obtained from the queue coupling by OPT's activation of arm $i$ are i.i.d. according to the uniform distribution." It makes the coupling a valid representation of OPT, so OPT's expected reward can be computed on the coupled space.
--
--   Differences from the source:
--   - reading: the samples obtained by OPT's activation of arm i are i.i.d. uniform → clause 1: each seed OPT uses is uniform and independent of OPT's observations before the draw and of all earlier seeds OPT used (all arms); reason: conditional uniformity given everything earlier is the i.i.d. property of the sequence (and slightly more: independence from OPT's observations), which is what the proof of Theorem 2 needs
--   - generalization: Lemma 1 as printed → an additional clause 2: OPT's history has the same law in the coupled run as in its own run; reason: clause 2 is the consequence of clause 1 the proof of Theorem 2 uses; dropping it gives the printed statement
--   - encoding: the queue coupling of p.20 (fresh U[0,1] sample when Q_i is empty) → coupledRun: π's step then OPT's step in each period; OPT's fresh seed comes from its own tape; reason: the same construction on the tape space
--   - encoding: periods t = 1, …, T → periods t = 0, …, T − 1 (t < T); reason: Lean indexing; the same periods shifted by one
--   - encoding: online policies, randomizing over available action sets adapted to the available information → Rule: an initial seed s ∼ seedLaw and a per-period uniform seed; proposals that are not available sets of 𝒜_t are replaced by ∅; IsAdmissible = seedLaw a probability measure and the proposal measurable in the seeds; reason: a seed can encode any randomization; measurability makes the expectation of a randomized policy meaningful; GRD-R's random threshold is its initial seed
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, §3.2, Lemma 1, p.20 (proof p.38)

import Mathlib
import Definitions.Def_GreedyReusableNet_IsAdmissible
import Definitions.Def_GreedyReusableNet_coupledRun
import Definitions.Def_GreedyReusableNet_tapeLaw

open MeasureTheory

namespace GreedyReusableNet

/-- **Lemma 1 (validity of the queue coupling)** (Simchi-Levi, Zheng & Zhu, SSRN 3981123, §3.2,
p.20; proof p.38): "For any arm `i ∈ [N]`, the samples obtained from the queue coupling by OPT's
activation of arm `i` are i.i.d. according to the uniform distribution."

Let `π` and OPT `π'` be admissible policies, run in the queue coupling (`coupledRun`) on the
space `coupledLaw T π π'`.

1. For every period `t < T` and arm `i`, the seed OPT uses for `i` in period `t` is uniform on
   `[0, 1]` and independent of everything OPT has seen up to its blocking-time draw in period `t`
   (its history before `t`, its action set and its activated bundles at `t`) and of all seeds
   OPT used before `t`, on the event that OPT activates `i` at `t`.
2. Consequently OPT's history in the coupled run has the same law as in its own run.

**Formalization Note** "i.i.d. uniform" is stated as clause 1: conditionally on OPT's
observations and on its earlier seeds, each new seed is uniform; this gives independence and
uniformity of the whole sequence. Clause 2 is the form in which the proof of Theorem 2 uses the
lemma. OPT's information takes countably many values, so conditioning on each value `x`
suffices. -/
theorem lemma_1 {N T : ℕ} (I : ProblemInstance N) (π π' : Rule N)
    (hπ : IsAdmissible π) (hπ' : IsAdmissible π') :
    (∀ t < T, ∀ (i : Fin N)
      (x : History N × Finset (Finset (Fin N)) × Finset (Finset (Fin N)))
      (E : Set (Fin t → Fin N → ℝ)), MeasurableSet E → ∀ U : Set ℝ, MeasurableSet U →
      coupledLaw T π π' {ω |
          ((coupledFinal I T π π' ω).2.1.take t, actionAt (coupledFinal I T π π' ω).2.1 t,
            activatedAt (coupledFinal I T π π' ω).2.1 t) = x ∧
          (fun k : Fin t => (coupledFinal I T π π' ω).2.2.2.getD k (fun _ => 0)) ∈ E ∧
          i ∈ activatedArms (activatedAt (coupledFinal I T π π' ω).2.1 t) ∧
          (coupledFinal I T π π' ω).2.2.2.getD t (fun _ => 0) i ∈ U} =
        coupledLaw T π π' {ω |
          ((coupledFinal I T π π' ω).2.1.take t, actionAt (coupledFinal I T π π' ω).2.1 t,
            activatedAt (coupledFinal I T π π' ω).2.1 t) = x ∧
          (fun k : Fin t => (coupledFinal I T π π' ω).2.2.2.getD k (fun _ => 0)) ∈ E ∧
          i ∈ activatedArms (activatedAt (coupledFinal I T π π' ω).2.1 t)} * unif U) ∧
    ∀ h : History N,
      coupledLaw T π π' {ω | (coupledFinal I T π π' ω).2.1 = h} =
        (π'.seedLaw.prod (tapeLaw N T)) {p | run I (π'.act p.1) p.2 T = h} := by sorry

end GreedyReusableNet
