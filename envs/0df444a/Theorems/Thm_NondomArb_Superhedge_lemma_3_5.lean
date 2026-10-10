-- Prove2me | Theorems.Thm_NondomArb_Superhedge_lemma_3_5
-- name    : NondomArb.Superhedge.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:24:03.641194+00:00
-- url     : https://prove2.me/theorems/44590b04-3a32-43bb-aa55-1a9bff8ce1ec
-- title:
--   Lemma 3.5 — if π(f) = 0, there are R_n ⋘ 𝒫 with E_{R_n}[ΔS] → 0 and E_{R_n}[f] → 0
-- statement:
--   Consider the one-period market of §3 (nonempty convex $\mathcal P$, measurable increment $\Delta S$), and let $\pi(f)$ be the superhedging price (3.2).
--
--   **Lemma.** Let NA($\mathcal P$) hold and let $f$ be a random variable with $\pi(f)=0$. There exist probabilities $R_n\lll\mathcal P$, $n\ge1$, such that
--   $$E_{R_n}[\Delta S]\to0\qquad\text{and}\qquad E_{R_n}[f]\to0 .$$
--
--   The $R_n$ are "approximate martingale measures" that nearly attain the price; Lemma 3.6 then perturbs them into true martingale measures.
--
--   **Formalization Note** The $R_n$ are required to satisfy $E_{R_n}[|\Delta S|+|f|]<\infty$, so that both expectations are finite real numbers (Bochner integrals); the paper's proof produces such $R_n$ (they lie in its set $\Theta$).
-- source:
--   Bouchard, Nutz, Arbitrage and duality in nondominated discrete-time models, arXiv:1305.6008v3, p. 15, Lemma 3.5

import Mathlib
import Definitions.Def_NondomArb_Superhedge_Basic
import Definitions.Def_NondomArb_Superhedge_OnePeriod
open MeasureTheory Filter Topology NondomArb.Superhedge.OnePeriod

namespace NondomArb.Superhedge

/-- **Lemma 3.5** (p. 15). Under NA(𝒫), if `π(f) = 0` there are probabilities `R_n ⋘ 𝒫` with
`E_{R_n}[ΔS] → 0` and `E_{R_n}[f] → 0`; the `R_n` are taken with `E_{R_n}[|ΔS| + |f|] < ∞` (so that
both expectations are finite), as the proof provides. -/
theorem lemma_3_5 {Ω : Type*} [MeasurableSpace Ω] (Pset : Set (Measure Ω))
    (hP : IsConvexModelSet Pset) {d : ℕ} (ΔS : Ω → (Fin d → ℝ)) (hΔS : Measurable ΔS)
    (hNA : NA Pset ΔS) (f : Ω → ℝ) (hf : Measurable f) (hπ : price Pset ΔS f = 0) :
    ∃ R : ℕ → Measure Ω, (∀ n, R n ∈ Theta Pset ΔS f) ∧
      Tendsto (fun n => ∫ ω, ΔS ω ∂ (R n)) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ ω, f ω ∂ (R n)) atTop (𝓝 0) := by sorry

end NondomArb.Superhedge
