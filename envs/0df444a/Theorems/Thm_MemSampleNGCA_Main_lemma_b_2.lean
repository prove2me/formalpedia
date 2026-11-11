-- Prove2me | Theorems.Thm_MemSampleNGCA_Main_lemma_b_2
-- name    : MemSampleNGCA.Main.lemma_b_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:42:01.946207+00:00
-- url     : https://prove2.me/theorems/92cc9074-69b9-426f-a571-4d0c1d21d561
-- title:
--   Lemma B.2 — KL(µ_N, ν_N) ≤ N · max_{i∈[N]} Σ_v KL(P_{ρ_{i,v}}, P_0) · µ_i(v)
-- statement:
--   Let $\pi$ be a probability measure on $\Theta$ and $P_0$ one on $\mathcal X$, and let $\{P_\theta\}$ have densities $0\le dP_\theta/dP_0\le M$ (the setting of Theorem B.1). For every single-pass streaming algorithm with $B$ bits of memory run on $N$ samples, with $\mu_i,\nu_i$ the state laws (14) and $P_{\rho_{i,v}}$ the posterior mixtures (18),
--   $$\mathrm{KL}(\mu_N,\nu_N)\le N\cdot\max_{i\in[N]}\sum_{v\in\{0,1\}^B}\mathrm{KL}\big(P_{\rho_{i,v}},P_0\big)\cdot\mu_i(v).$$
--
--   The lemma reduces the information carried by the final memory state to the per-step information of one sample given the current state. It is the first step of the proof of Theorem B.1.
--
--   Differences from the source:
--   - generalization: π is the uniform measure on Θ ⊆ S^{d−1} → π is any probability measure on a measurable space Θ; reason: the statement and proof use only that π is a probability measure; the uniform measure is an instance
--   - generalization: the setting of Theorem B.1 includes q ≥ 2 and h ≥ 1 → no hypotheses on q, h; reason: q and h do not occur in (19)
--   - encoding: a family {P_θ} with 0 ≤ dP_θ/dP_0 ≤ M → P_θ = p(θ,·)·P_0 with p ≥ 0 jointly measurable, ∫ p(θ,·) dP_0 = 1, p(θ,·) ≤ M P_0-a.e. (IsBoundedDensityFamily); reason: every such family has this form; joint measurability is what makes ∫ P_θ π(dθ) meaningful
--   - encoding: Definition 1.7 → StreamingAlg (states Fin B → Bool, seeds from an arbitrary probability space (Ω, R), measurable Upd and Out); reason: measurability is needed for the probabilities to exist
--   - encoding: KL and probabilities real → klDiv and all quantities in ℝ≥0∞, µ_N and ν_N as measures Σ_v µ_N(v) δ_v on {0,1}^B, max as Finset.sup; reason: same values; a term with µ_i(v) = 0 is 0, as in the paper
--   - encoding: P_{ρ_{i,v}} = ∫ P_θ ρ_{i,v}(θ) π(dθ) → P_0 with density x ↦ ∫ p(θ, x) ρ_{i,v}(θ) π(dθ); reason: the same measure by Tonelli
-- source:
--   Pensia, Gupta, Verchand, Sharan, Vedantam, Memory-Sample Tradeoffs in High-Dimensional Statistics, STOC 2027 submission (manuscript sha256 ac94994a…), p. 17 (PDF 19), Lemma B.2

import Mathlib
import Definitions.Def_MemSampleNGCA_Main_Streaming
import Definitions.Def_MemSampleNGCA_Main_Framework

open MeasureTheory
open scoped ENNReal

namespace MemSampleNGCA.Main

/-- Lemma B.2 (p. 17, PDF 19): under the setting of Theorem B.1,
`KL(µ_N, ν_N) ≤ N · max_{i ∈ [N]} Σ_v KL(P_{ρ_{i,v}}, P₀) · µ_i(v)`. -/
theorem lemma_b_2 {Θ : Type*} [MeasurableSpace Θ] {X : Type*} [MeasurableSpace X]
    {B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (π : Measure Θ) (P₀ : Measure X) (p : Θ → X → ℝ) (M : ℝ)
    (hF : IsBoundedDensityFamily π P₀ p M)
    (A : StreamingAlg B X Ω) (N : ℕ) :
    InformationTheory.klDiv (muMeas A N π P₀ p N) (nuMeas A N P₀ N) ≤
      (N : ℝ≥0∞) * (Finset.Icc 1 N).sup (fun i =>
        ∑ v, InformationTheory.klDiv (Prho A N π P₀ p i v) P₀ * mu A N π P₀ p i v) := by sorry

end MemSampleNGCA.Main
