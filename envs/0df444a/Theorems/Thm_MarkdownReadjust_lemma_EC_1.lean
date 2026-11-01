-- Prove2me | Theorems.Thm_MarkdownReadjust_lemma_EC_1
-- name    : MarkdownReadjust.lemma_EC_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:17:23.605985+00:00
-- url     : https://prove2.me/theorems/48d643fa-e24c-4760-bee0-313df79d4ed6
-- title:
--   Lemma EC.1 — bounds on $A_1$ and $A_2$
-- statement:
--   In the setting of Theorem 4, with $\theta=(x_0+1)^{-1/(N+2)}$,
--
--   $$
--   A_1\le(\rho^d+1)\,\lambda T\,\mathbb P(\mathcal G^c),
--   $$
--
--   $$
--   A_2\le 5(\ln(x_0+1))^{2\alpha}\frac{N+1}{\theta}+\frac N\theta+\lambda T\Big(\max\Big\{\rho^d,\ N(\ln(x_0+1))^\alpha\frac{(x_0+1)^{1/2}}{(\lambda T)^{1/2}}+N(x_0+1)^{\frac1{N+2}}\Big\}\Big)^2\,\mathbb P(\mathcal G^c),
--   $$
--
--   where $\mathbb P$ is the law of the uncapped process and $\mathcal G$ the good event.
--
--   Together with the Taylor bound after (EC.2), these bounds give the revenue loss of the uncapped process up to the probability of the bad event.
--
--   Differences from the source:
--   - generalization: valuation c.d.f. F with a density f whose derivative f′ is supported on [0,V), A1–A3 → F̄ continuous and strictly decreasing on [0,V] with F̄(0)=1, F̄(V)=0, plus A2 for R(ρ)=ρF̄⁻¹(ρ) on [0,1], |R| ≤ C on [0,1], and A3's twice differentiability with |R′|, |R″| ≤ C on the open interval (0,1) only; reason: the results use F̄ only through these properties (A1 follows from continuity at V); every model of the paper satisfies them, and nothing is required of R′, R″ at the endpoints ρ = 0, 1
--   - encoding: expectations and probabilities of the uncapped process (Ŝₙ Poisson with mean λ(t_{n+1}−tₙ)ρ̂ₙ) → integrals and measures under hatLaw, the sequential Poisson law of (Ŝ₀,…,Ŝ_N) on Fin (N+1) → ℕ; reason: it is the joint law of the uncapped sales; same values
--   - generalization: the k-th problem of the asymptotic setting (k suppressed, p.9) → every instance (x₀, T) satisfying InSetting (x₀ ≥ 1, T > 0, N ≥ 1, α > 1/2, the N condition, ρᵈ > η₀, λT > 1); reason: each k-th problem satisfying the setting is such an instance
-- source:
--   Chen, Jasin, Simple monotonic readjustment policies with applications to markdown pricing and pricing in the presence of strategic customers, SSRN 3740871 (2023-10-09), Lemma EC.1, pp.ec13–ec14

import Mathlib
import Definitions.Def_MarkdownReadjust_Model
import Definitions.Def_MarkdownReadjust_rhoD
import Definitions.Def_MarkdownReadjust_tgrid
import Definitions.Def_MarkdownReadjust_hatLaw
import Definitions.Def_MarkdownReadjust_goodEvent
import Definitions.Def_MarkdownReadjust_A1
import Definitions.Def_MarkdownReadjust_A2
import Definitions.Def_MarkdownReadjust_InSetting

open MeasureTheory

namespace MarkdownReadjust

/-- **Lemma EC.1, pp.ec13–ec14** (Chen–Jasin, SSRN 3740871). In the setting of Theorem 4,
`A₁ ≤ (ρᵈ + 1) λT P(𝒢ᶜ)` and
`A₂ ≤ 5(ln(x₀+1))^{2α}(N+1)/θ + N/θ
  + λT (max{ρᵈ, N(ln(x₀+1))^α (x₀+1)^{1/2}/(λT)^{1/2} + N(x₀+1)^{1/(N+2)}})² P(𝒢ᶜ)`,
with `θ = (x₀+1)^{−1/(N+2)}`.

**Formalization Note.** `P` is the uncapped law `hatLaw`; `P(𝒢ᶜ)` is its real value
(`Measure.real`, a probability, hence finite). `(·)^{1/2}` is `Real.sqrt`. -/
theorem lemma_EC_1 (M : Model) (α : ℝ) (N x : ℕ) (τ : ℝ) (h : InSetting M α N x τ) :
    A1 M α N x τ
        ≤ (rhoD M x τ + 1) * M.lam * τ * (hatLaw M α N x τ).real (goodEvent M α N x τ)ᶜ ∧
      A2 M α N x τ
        ≤ 5 * Real.log ((x : ℝ) + 1) ^ (2 * α) * ((N : ℝ) + 1) / theta x N + (N : ℝ) / theta x N
          + M.lam * τ *
              (max (rhoD M x τ)
                ((N : ℝ) * Real.log ((x : ℝ) + 1) ^ α * Real.sqrt ((x : ℝ) + 1)
                    / Real.sqrt (M.lam * τ)
                  + (N : ℝ) * ((x : ℝ) + 1) ^ ((1 : ℝ) / ((N : ℝ) + 2)))) ^ 2
            * (hatLaw M α N x τ).real (goodEvent M α N x τ)ᶜ := by sorry

end MarkdownReadjust
