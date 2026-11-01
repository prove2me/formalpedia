-- Prove2me | Theorems.Thm_MarkdownReadjust_lemma_EC_3
-- name    : MarkdownReadjust.lemma_EC_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:17:09.949989+00:00
-- url     : https://prove2.me/theorems/0fb3ed9d-fd5c-40d5-a7e3-a2a4e69b11b3
-- title:
--   Lemma EC.3 — expected overselling of the uncapped process
-- statement:
--   In the setting of Theorem 4,
--
--   $$
--   \mathsf E\Big[\Big(\sum_{n=0}^{N}\hat S_n-x_0\Big)^+\Big]\le\frac12(\lambda T)^{\frac12}(x_0+1)^{-\frac N{2(N+2)}}+(\lambda T+1)\,\mathbb P(\mathcal G^c)^{\frac12},
--   $$
--
--   where $\mathsf E$, $\mathbb P$ refer to the uncapped process. This bounds the second term of (EC.2).
--
--   Differences from the source:
--   - generalization: valuation c.d.f. F with a density f whose derivative f′ is supported on [0,V), A1–A3 → F̄ continuous and strictly decreasing on [0,V] with F̄(0)=1, F̄(V)=0, plus A2 for R(ρ)=ρF̄⁻¹(ρ) on [0,1], |R| ≤ C on [0,1], and A3's twice differentiability with |R′|, |R″| ≤ C on the open interval (0,1) only; reason: the results use F̄ only through these properties (A1 follows from continuity at V); every model of the paper satisfies them, and nothing is required of R′, R″ at the endpoints ρ = 0, 1
--   - encoding: expectations and probabilities of the uncapped process (Ŝₙ Poisson with mean λ(t_{n+1}−tₙ)ρ̂ₙ) → integrals and measures under hatLaw, the sequential Poisson law of (Ŝ₀,…,Ŝ_N) on Fin (N+1) → ℕ; reason: it is the joint law of the uncapped sales; same values
--   - generalization: the k-th problem of the asymptotic setting (k suppressed, p.9) → every instance (x₀, T) satisfying InSetting (x₀ ≥ 1, T > 0, N ≥ 1, α > 1/2, the N condition, ρᵈ > η₀, λT > 1); reason: each k-th problem satisfying the setting is such an instance
--   - encoding: E[(Σ Ŝₙ − x₀)⁺] → lower Lebesgue integral ∫⁻ of ofReal of the overflow; reason: expectation of a nonnegative variable; the bound also asserts finiteness
-- source:
--   Chen, Jasin, Simple monotonic readjustment policies with applications to markdown pricing and pricing in the presence of strategic customers, SSRN 3740871 (2023-10-09), Lemma EC.3, p.ec14

import Mathlib
import Definitions.Def_MarkdownReadjust_Model
import Definitions.Def_MarkdownReadjust_seqPoissonLaw
import Definitions.Def_MarkdownReadjust_hatLaw
import Definitions.Def_MarkdownReadjust_goodEvent
import Definitions.Def_MarkdownReadjust_InSetting

open MeasureTheory

namespace MarkdownReadjust

/-- **Lemma EC.3, p.ec14** (Chen–Jasin, SSRN 3740871). In the setting of Theorem 4,
`E[(Σ_{n=0}^{N} Ŝₙ − x₀)⁺] ≤ ½ (λT)^{1/2} (x₀+1)^{−N/(2(N+2))} + (λT + 1) P(𝒢ᶜ)^{1/2}`.

**Formalization Note.** The expectation is the lower Lebesgue integral `∫⁻` of the nonnegative
overflow under the uncapped law `hatLaw`, so the bound also asserts its finiteness (no junk-zero
Bochner value). `P(𝒢ᶜ)` is `Measure.real`; `(·)^{1/2}` is `Real.sqrt`. -/
theorem lemma_EC_3 (M : Model) (α : ℝ) (N x : ℕ) (τ : ℝ) (h : InSetting M α N x τ) :
    ∫⁻ ω, ENNReal.ofReal (max ((∑ n ∈ Finset.range (N + 1), (pathExt ω n : ℝ)) - x) 0)
        ∂(hatLaw M α N x τ)
      ≤ ENNReal.ofReal (1 / 2 * Real.sqrt (M.lam * τ)
            * ((x : ℝ) + 1) ^ (-(N : ℝ) / (2 * ((N : ℝ) + 2)))
          + (M.lam * τ + 1) * Real.sqrt ((hatLaw M α N x τ).real (goodEvent M α N x τ)ᶜ)) := by sorry

end MarkdownReadjust
