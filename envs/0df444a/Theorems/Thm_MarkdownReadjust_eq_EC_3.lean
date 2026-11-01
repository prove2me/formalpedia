-- Prove2me | Theorems.Thm_MarkdownReadjust_eq_EC_3
-- name    : MarkdownReadjust.eq_EC_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:16:49.351334+00:00
-- url     : https://prove2.me/theorems/f4844d49-bef9-4454-9d59-893bc89b0abc
-- title:
--   (EC.3) — closed form of $\hat\rho_n$ on the good event
-- statement:
--   In the setting of Theorem 4, on the good event $\mathcal G$, for all $n=0,\dots,N$,
--
--   $$
--   \hat\rho_n=\rho^d-\eta_n-\sum_{m=0}^{n-1}\frac{\hat\Delta_m}{\lambda(T-t_{m+1})}>0 .
--   $$
--
--   On $\mathcal G$ the projection and the maximum in the definition of $\hat\rho_n$ are inactive, so the adjusted rates are affine in the past sales deviations.
--
--   Differences from the source:
--   - generalization: valuation c.d.f. F with a density f whose derivative f′ is supported on [0,V), A1–A3 → F̄ continuous and strictly decreasing on [0,V] with F̄(0)=1, F̄(V)=0, plus A2 for R(ρ)=ρF̄⁻¹(ρ) on [0,1], |R| ≤ C on [0,1], and A3's twice differentiability with |R′|, |R″| ≤ C on the open interval (0,1) only; reason: the results use F̄ only through these properties (A1 follows from continuity at V); every model of the paper satisfies them, and nothing is required of R′, R″ at the endpoints ρ = 0, 1
--   - encoding: conditional on 𝒢 → for every path ω ∈ 𝒢; reason: the claim is a pathwise identity on the event
--   - generalization: the k-th problem of the asymptotic setting (k suppressed, p.9) → every instance (x₀, T) satisfying InSetting (x₀ ≥ 1, T > 0, N ≥ 1, α > 1/2, the N condition, ρᵈ > η₀, λT > 1); reason: each k-th problem satisfying the setting is such an instance
-- source:
--   Chen, Jasin, Simple monotonic readjustment policies with applications to markdown pricing and pricing in the presence of strategic customers, SSRN 3740871 (2023-10-09), Appendix B.1, eq. (EC.3), p.ec13

import Mathlib
import Definitions.Def_MarkdownReadjust_Model
import Definitions.Def_MarkdownReadjust_rhoD
import Definitions.Def_MarkdownReadjust_tgrid
import Definitions.Def_MarkdownReadjust_eta
import Definitions.Def_MarkdownReadjust_seqPoissonLaw
import Definitions.Def_MarkdownReadjust_hatLaw
import Definitions.Def_MarkdownReadjust_goodEvent
import Definitions.Def_MarkdownReadjust_InSetting

namespace MarkdownReadjust

/-- **(EC.3), p.ec13** (Chen–Jasin, SSRN 3740871). In the setting of Theorem 4, conditional on
the good event `𝒢`,
`ρ̂ₙ = ρᵈ − ηₙ − Σ_{m=0}^{n−1} Δ̂ₘ/(λ(T − t_{m+1})) > 0` for all `n = 0, ⋯, N`.

**Formalization Note.** "Conditional on 𝒢" is read pathwise: for every uncapped sales path
`ω ∈ 𝒢`. -/
theorem eq_EC_3 (M : Model) (α : ℝ) (N x : ℕ) (τ : ℝ) (h : InSetting M α N x τ) :
    ∀ ω ∈ goodEvent M α N x τ, ∀ n : ℕ, n ≤ N →
      rhoHat M α N x τ (pathExt ω) n
          = rhoD M x τ - eta M.lam α x τ N n
            - ∑ m ∈ Finset.range n,
                DeltaHat M α N x τ (pathExt ω) m / (M.lam * (τ - tgrid x τ N (m + 1))) ∧
        0 < rhoHat M α N x τ (pathExt ω) n := by sorry

end MarkdownReadjust
