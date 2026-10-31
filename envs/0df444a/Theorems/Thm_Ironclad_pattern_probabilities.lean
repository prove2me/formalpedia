-- Prove2me | Theorems.Thm_Ironclad_pattern_probabilities
-- name    : Ironclad.pattern_probabilities
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:26:27.332985+00:00
-- url     : https://prove2.me/theorems/ce80a07b-f4f3-40b3-962a-f7c37906fd55
-- title:
--   p.9 display — occurrence probabilities $\mathbb P(\sigma_i)$ and expected lengths $\mathbb E|\sigma_i|$ of the patterns
-- statement:
--   Let $0<p_h<1$, $0<q<1$, $\Delta\ge1$, write $q_h=(1-q)p_h$, $q_H=qp_h$, and let $w=(w_t)_{t\ge0}$ be an i.i.d. honest characteristic string with these parameters. Fix a slot $t$ and a pattern type $\sigma\in\{\sigma_1,\sigma_2,\sigma_3,\sigma_4\}$, and let $|\sigma|_t$ be the length of the pattern of type $\sigma$ that starts at slot $t$ under the greedy rule of Definition 3.1 (and $0$ if no such pattern starts at $t$). Then
--
--   $$
--   \Pr(\text{a pattern of type }\sigma\text{ starts at }t)=\mathbb P(\sigma),\qquad \mathbb E\big[|\sigma|_t\big]=\mathbb P(\sigma)\,\mathbb E|\sigma|,
--   $$
--
--   with $|\sigma|_t$ integrable, where
--
--   $$
--   \mathbb P(\sigma_1)=q_h[1-(1-p_h)^\Delta],\quad \mathbb E|\sigma_1|=\frac1{p_h}-\frac{\Delta(1-p_h)^\Delta}{1-(1-p_h)^\Delta},\qquad \mathbb P(\sigma_2)=q_h(1-p_h)^\Delta,\quad \mathbb E|\sigma_2|=\frac1{p_h}+\Delta,
--   $$
--   $$
--   \mathbb P(\sigma_3)=q_H[1-(1-q_H)^\Delta],\quad \mathbb E|\sigma_3|=\frac1{q_H}-\frac{\Delta(1-q_H)^\Delta}{1-(1-q_H)^\Delta},\qquad \mathbb P(\sigma_4)=q_H(1-q_H)^\Delta,\quad \mathbb E|\sigma_4|=\frac1{p_h}+\Delta.
--   $$
--
--   In words, $\mathbb E|\sigma|$ is the expected length of a pattern of type $\sigma$ given that it occurs. These are the inputs of the transition matrix (3) and of the edge lengths $l_{ij}$.
--
--   **Formalization Note** "A pattern of type $\sigma$ starts at $t$" is the slot-local event that $w_t\neq0$ and the greedy rule applied at $t$ produces $\sigma$; it does not require $t$ to be a start of the decomposition from slot $0$.
--
--   Differences from the source:
--   - reading: $\sigma_3=\{H\}\|\{0,h\}^k$, $k\le\Delta$ (Definition 3.1) → $k<\Delta$; reason: the printed $\mathbb P(\sigma_3)=q_H[1-(1-q_H)^\Delta]$ and $\mathbb P(\sigma_4)=q_H(1-q_H)^\Delta$ on the same page, and App. .1.1's "$Z<\Delta$", hold only for $k<\Delta$ (with $k\le\Delta$, $\sigma_3$ would have probability $q_H[1-(1-q_H)^{\Delta+1}]$ and overlap $\sigma_4$)
--   - reading: "the probability of the occurrence and the expected length of $\sigma_i$" → the probability that a $\sigma_i$ pattern starts at a fixed slot, and $\mathbb E[|\sigma_i|_t]=\mathbb P(\sigma_i)\mathbb E|\sigma_i|$ with integrability; reason: this is the conditional expectation App. .1.1 computes, written without dividing by $\mathbb P(\sigma_i)$
--   - reading: no parameter range on p.9 → $0<p_h<1$, $0<q<1$, $\Delta\ge1$; reason: the "proper parameters" of Theorem 3.2 (p.14); at $q=0$ the printed $\mathbb E|\sigma_3|$ divides by zero
--   - encoding: the i.i.d. law of §2.1 → hypotheses (measurable, mutually independent, each with the one-slot law) on an arbitrary probability space; slots indexed from $0$; reason: Lean convention, same instances
-- source:
--   Zhang, Gong, Li, Wu & Zhang, Improving Blockchain Consistency by Assigning Weights to Random Blocks, arXiv:2107.10467v2, p.9 (display "The probability of the occurrence and the expected length of σi"), with Appendix .1.1, p.29

import Mathlib
import Definitions.Def_Ironclad_Model
import Definitions.Def_Ironclad_Decomposition
import Definitions.Def_Ironclad_ClosedForms

open MeasureTheory ProbabilityTheory Filter Topology

namespace Ironclad

/-- The occurrence probabilities and expected lengths of the four patterns,
Zhang, Gong, Li, Wu & Zhang,
*Improving Blockchain Consistency by Assigning Weights to Random Blocks*, arXiv:2107.10467v2, p.9 (display after the notation `q_h, q_H`) and Appendix .1.1, p.29.
For every slot `t` and pattern type `σ`: the probability that a pattern of type `σ` starts at
slot `t` is `P(σ)`, and the expected length of that pattern on this event is `P(σ) E[|σ|]`,
i.e. `E[|σ|]` is the expected length of `σ` given that it occurs.

**Formalization Note** "A pattern of type `σ` starts at `t`" is the slot-local event
`step Δ x t = some (σ, e)` of the greedy rule (`Ironclad.step`); `slotLen` is the pattern's length
on that event and `0` off it. The i.i.d. honest string is
`IsHonestString μ w ph q` on an arbitrary probability space; slots are indexed from `0`; the
standing parameter range `0 < p_h, q < 1`, `Δ ≥ 1` is that of Theorem 3.2. -/
theorem pattern_probabilities {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (w : ℕ → Ω → Sym) (ph q : ℝ) (Δ : ℕ) (hph0 : 0 < ph) (hph1 : ph < 1) (hq0 : 0 < q)
    (hq1 : q < 1) (hΔ : 1 ≤ Δ) (hw : IsHonestString μ w ph q) (t : ℕ) (σ : Pat) :
    μ.real {ω | ∃ e, step Δ (fun n => w n ω) t = some (σ, e)} = patProb ph q Δ σ ∧
    Integrable (fun ω => slotLen Δ (fun n => w n ω) t σ) μ ∧
    ∫ ω, slotLen Δ (fun n => w n ω) t σ ∂μ = patProb ph q Δ σ * patMeanLen ph q Δ σ := by sorry

end Ironclad
