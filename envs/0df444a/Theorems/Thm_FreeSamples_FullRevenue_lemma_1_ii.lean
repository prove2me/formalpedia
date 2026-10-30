-- Prove2me | Theorems.Thm_FreeSamples_FullRevenue_lemma_1_ii
-- name    : FreeSamples.FullRevenue.lemma_1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T13:55:37.074046+00:00
-- url     : https://prove2.me/theorems/a583b195-e755-4764-95cc-327c7c65fa18
-- title:
--   Lemma 1(ii) — both full-filtration conditional mean drifts at every time
-- statement:
--   In the Gaussian model, let $m_t,v_t$ be the Buyer posterior mean and variance, and let the observer's posterior mean displacement from $m_t$ be $g_t^i$: it is zero for the Buyer and $g_t=\widetilde m_t-m_t$ for the Seller. The noise variance is $n>0$. For every deterministic $t\ge0$ and every $h\ge0$, the increment is integrable and
--   $$\mathbb E^i[m_{t+h}-m_t\mid\mathcal F_t]=g_t^i\frac{v_{t+h}}n h\quad\text{almost surely}.$$
--   The displayed right side fixes a coherent conditional version as a function of $h$. Its right derivative at zero is
--   $$\left.\frac{d}{dh}\right|_{0+}\mathbb E^i[m_{t+h}-m_t\mid\mathcal F_t]=\frac{g_t^iv_t}n.$$
--   This simultaneously retains the Buyer's zero conditional drift and the Seller's conditional persuasion drift at every time, under the entire observed-data filtration.
--
--   Differences from the source:
--   - reading: conditional infinitesimal mean increments → right derivatives at h=0 of a coherent conditional-increment version, at every deterministic t; reason: finite positive increments do not equal their first-order drift
--   - generalization: the first-order conditional drift → also the exact integrable finite-increment identity for every h≥0; reason: the Gaussian posterior formula and p.29 calculation yield it and its derivative recovers both source clauses
--   - encoding: the Buyer and Seller conditional expectations → one perspective parameter and the whole natural signal filtration, with per-time almost-sure equality; reason: this combines the two clauses without changing the measures or claiming a simultaneous null set for all t
-- source:
--   Drakopoulos & Makhdoumi, Providing Data Samples for Free, SSRN 3611003, pinned local PDF snapshot (creation metadata 2021-08-30; SHA-256 2e29ad6e37639d93e587e9999f63959d3eb52c66a1fe2ac7e78f3d33976e44c0), p.14, Lemma 1(ii); p.29, proof

import Definitions.Def_FreeSamples_FullRevenue_Learning

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace FreeSamples.FullRevenue

/-- Lemma 1(ii), p.14, with exact finite conditional increments to fix a
coherent version before taking the right derivative. -/
theorem lemma_1_ii (p : Revenue.Params) (i : Perspective)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (θ : Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ)
    (hM : Revenue.IsModel P (priorMean p i) (priorVariance p i) θ B) (t : ℝ≥0) :
    (∀ h : ℝ≥0,
      Integrable (fun ω => posteriorMean p θ B (t + h) ω - posteriorMean p θ B t ω) P ∧
      P[(fun ω => posteriorMean p θ B (t + h) ω - posteriorMean p θ B t ω) |
        Revenue.dataFiltration p.σsq θ B hM.meas_θ hM.meas_B t] =ᵐ[P]
        fun ω => currentGap p i t (Revenue.Y p.σsq θ B t ω) * p.buyerVar (t + h) / p.σsq * h) ∧
    ∀ᵐ ω ∂P,
      HasDerivWithinAt
        (fun h : ℝ => currentGap p i t (Revenue.Y p.σsq θ B t ω) *
          p.buyerVar ((t : ℝ) + h) / p.σsq * h)
        (currentGap p i t (Revenue.Y p.σsq θ B t ω) * p.buyerVar t / p.σsq)
        (Set.Ici 0) 0 := by sorry

end FreeSamples.FullRevenue
