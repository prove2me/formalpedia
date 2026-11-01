-- Prove2me | Theorems.Thm_MarkdownReadjust_eq_EC_2
-- name    : MarkdownReadjust.eq_EC_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:16:16.973994+00:00
-- url     : https://prove2.me/theorems/ae885e43-a812-4e53-a006-4a9bfb9f4fbe
-- title:
--   (EC.2) — revenue lower bound by the uncapped process
-- statement:
--   In the setting of Theorem 4, the expected revenue of the markdown readjustment policy satisfies
--
--   $$
--   J^{\pi^{\mathrm{Re}}_\searrow}(x_0,T)\ \ge\ \sum_{n=0}^{N}\mathsf E\big[\bar F^{-1}(\hat\rho_n)\,\hat S_n\big]-V\,\mathsf E\Big[\Big(\sum_{n=0}^{N}\hat S_n-x_0\Big)^+\Big],
--   $$
--
--   where the right side is computed for the uncapped process $(\hat\rho_n,\hat S_n)$ and $(\cdot)^+=\max\{\cdot,0\}$.
--
--   The policy agrees with the uncapped process until stock-out; the second term charges the price $V$ for every unit the uncapped process sells beyond the inventory. This reduces the analysis of the policy to a process without inventory constraint.
--
--   Differences from the source:
--   - generalization: valuation c.d.f. F with a density f whose derivative f′ is supported on [0,V), A1–A3 → F̄ continuous and strictly decreasing on [0,V] with F̄(0)=1, F̄(V)=0, plus A2 for R(ρ)=ρF̄⁻¹(ρ) on [0,1], |R| ≤ C on [0,1], and A3's twice differentiability with |R′|, |R″| ≤ C on the open interval (0,1) only; reason: the results use F̄ only through these properties (A1 follows from continuity at V); every model of the paper satisfies them, and nothing is required of R′, R″ at the endpoints ρ = 0, 1
--   - encoding: J^{π}(x₀,T) = E[∫₀ᵀ π_t dY_t] for the continuous-time Poisson arrival process → markdownRevenue: E[Σₙ F̄⁻¹(ρₙ)·min(Dₙ, Xₙ)] under the sequential Poisson law of the interval demand counts Dₙ; reason: Poisson thinning and independent increments: given the past, Dₙ is Poisson(λ(t_{n+1}−tₙ)ρₙ); same value
--   - encoding: expectations and probabilities of the uncapped process (Ŝₙ Poisson with mean λ(t_{n+1}−tₙ)ρ̂ₙ) → integrals and measures under hatLaw, the sequential Poisson law of (Ŝ₀,…,Ŝ_N) on Fin (N+1) → ℕ; reason: it is the joint law of the uncapped sales; same values
--   - generalization: the k-th problem of the asymptotic setting (k suppressed, p.9) → every instance (x₀, T) satisfying InSetting (x₀ ≥ 1, T > 0, N ≥ 1, α > 1/2, the N condition, ρᵈ > η₀, λT > 1); reason: each k-th problem satisfying the setting is such an instance
-- source:
--   Chen, Jasin, Simple monotonic readjustment policies with applications to markdown pricing and pricing in the presence of strategic customers, SSRN 3740871 (2023-10-09), Appendix B.1, eq. (EC.2), p.ec13

import Mathlib
import Definitions.Def_MarkdownReadjust_Model
import Definitions.Def_MarkdownReadjust_seqPoissonLaw
import Definitions.Def_MarkdownReadjust_markdownRevenue
import Definitions.Def_MarkdownReadjust_hatLaw
import Definitions.Def_MarkdownReadjust_InSetting

open MeasureTheory

namespace MarkdownReadjust

/-- **(EC.2), p.ec13** (Chen–Jasin, SSRN 3740871). In the setting of Theorem 4 (Appendix B.1),
`J^{π^Re_↘}(x₀, T) ≥ Σ_{n=0}^{N} E[F̄⁻¹(ρ̂ₙ) Ŝₙ] − V E[(Σ_{n=0}^{N} Ŝₙ − x₀)⁺]`,
where the expectations on the right are under the uncapped process (`hatLaw`).

**Formalization Note.** `Ŝₙ = pathExt ω n` under `hatLaw`; `(·)⁺ = max(·, 0)`. Both
expectations on the right are finite (each `Ŝₙ` has a Poisson law with mean at most `λT`), so
the Bochner integrals are the true expectations. -/
theorem eq_EC_2 (M : Model) (α : ℝ) (N x : ℕ) (τ : ℝ) (h : InSetting M α N x τ) :
    ∑ n ∈ Finset.range (N + 1),
        ∫ ω, M.Finv (rhoHat M α N x τ (pathExt ω) n) * (pathExt ω n : ℝ) ∂(hatLaw M α N x τ)
      - M.V * ∫ ω, max ((∑ n ∈ Finset.range (N + 1), (pathExt ω n : ℝ)) - x) 0
          ∂(hatLaw M α N x τ)
      ≤ markdownRevenue M α N x τ := by sorry

end MarkdownReadjust
