-- Prove2me | Theorems.Thm_MarkdownReadjust_first_term_bound
-- name    : MarkdownReadjust.first_term_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:17:22.937582+00:00
-- url     : https://prove2.me/theorems/d2596030-022e-49e4-82ed-28ece1ff355c
-- title:
--   Display after (EC.2) — second-order Taylor bound on the uncapped revenue
-- statement:
--   In the setting of Theorem 4,
--
--   $$
--   \sum_{n=0}^{N}\mathsf E\big[\bar F^{-1}(\hat\rho_n)\hat S_n\big]=\sum_{n=0}^{N}\lambda(t_{n+1}-t_n)\,\mathsf E\big[R(\hat\rho_n)\big]\ \ge\ \bar J(x_0,T)-R'(\rho^d)\,A_1-\frac C2\,A_2,
--   $$
--
--   where $A_1=(-\lambda)\sum_{n}(t_{n+1}-t_n)\mathsf E[\hat\rho_n-\rho^d]$, $A_2=\lambda\sum_n(t_{n+1}-t_n)\mathsf E[(\hat\rho_n-\rho^d)^2]$, and $C$ is the constant of A3.
--
--   This splits the revenue of the uncapped process into the fluid value and two error terms, bounded in Lemma EC.1.
--
--   Differences from the source:
--   - generalization: valuation c.d.f. F with a density f whose derivative f′ is supported on [0,V), A1–A3 → F̄ continuous and strictly decreasing on [0,V] with F̄(0)=1, F̄(V)=0, plus A2 for R(ρ)=ρF̄⁻¹(ρ) on [0,1], |R| ≤ C on [0,1], and A3's twice differentiability with |R′|, |R″| ≤ C on the open interval (0,1) only; reason: the results use F̄ only through these properties (A1 follows from continuity at V); every model of the paper satisfies them, and nothing is required of R′, R″ at the endpoints ρ = 0, 1
--   - encoding: expectations and probabilities of the uncapped process (Ŝₙ Poisson with mean λ(t_{n+1}−tₙ)ρ̂ₙ) → integrals and measures under hatLaw, the sequential Poisson law of (Ŝ₀,…,Ŝ_N) on Fin (N+1) → ℕ; reason: it is the joint law of the uncapped sales; same values
--   - generalization: the k-th problem of the asymptotic setting (k suppressed, p.9) → every instance (x₀, T) satisfying InSetting (x₀ ≥ 1, T > 0, N ≥ 1, α > 1/2, the N condition, ρᵈ > η₀, λT > 1); reason: each k-th problem satisfying the setting is such an instance
--   - encoding: the four-member chain of the display → the equality of its first and third members and the inequality between the third and last; reason: the intermediate member E[F̄⁻¹(ρ̂ₙ)λ(t_{n+1}−tₙ)ρ̂ₙ] equals the third by R(ρ)=ρF̄⁻¹(ρ); the chain's conclusion is kept
-- source:
--   Chen, Jasin, Simple monotonic readjustment policies with applications to markdown pricing and pricing in the presence of strategic customers, SSRN 3740871 (2023-10-09), Appendix B.1, display after (EC.2), p.ec13

import Mathlib
import Definitions.Def_MarkdownReadjust_Model
import Definitions.Def_MarkdownReadjust_rhoD
import Definitions.Def_MarkdownReadjust_fluidValue
import Definitions.Def_MarkdownReadjust_tgrid
import Definitions.Def_MarkdownReadjust_seqPoissonLaw
import Definitions.Def_MarkdownReadjust_hatLaw
import Definitions.Def_MarkdownReadjust_A1
import Definitions.Def_MarkdownReadjust_A2
import Definitions.Def_MarkdownReadjust_InSetting

open MeasureTheory

namespace MarkdownReadjust

/-- **Display after (EC.2), p.ec13** (Chen–Jasin, SSRN 3740871). In the setting of Theorem 4,
`Σ_{n=0}^{N} E[F̄⁻¹(ρ̂ₙ) Ŝₙ] = Σ_{n=0}^{N} λ(t_{n+1} − tₙ) E[R(ρ̂ₙ)]
  ≥ J̄(x₀, T) − R′(ρᵈ) A₁ − (C/2) A₂`.

**Formalization Note.** Expectations are under the uncapped law `hatLaw`. `R′(ρᵈ)` is the
derivative of `R` within `[0,1]` at `ρᵈ ∈ (0,1)` (an interior point). The intermediate equality
`E[F̄⁻¹(ρ̂ₙ)Ŝₙ] = E[F̄⁻¹(ρ̂ₙ)λ(t_{n+1} − tₙ)ρ̂ₙ]` of the display is contained in the first
conjunct. -/
theorem first_term_bound (M : Model) (α : ℝ) (N x : ℕ) (τ : ℝ) (h : InSetting M α N x τ) :
    ∑ n ∈ Finset.range (N + 1),
        ∫ ω, M.Finv (rhoHat M α N x τ (pathExt ω) n) * (pathExt ω n : ℝ) ∂(hatLaw M α N x τ)
      = ∑ n ∈ Finset.range (N + 1), M.lam * (tgrid x τ N (n + 1) - tgrid x τ N n) *
          ∫ ω, M.R (rhoHat M α N x τ (pathExt ω) n) ∂(hatLaw M α N x τ) ∧
    fluidValue M x τ - derivWithin M.R (Set.Icc 0 1) (rhoD M x τ) * A1 M α N x τ
        - M.C / 2 * A2 M α N x τ
      ≤ ∑ n ∈ Finset.range (N + 1), M.lam * (tgrid x τ N (n + 1) - tgrid x τ N n) *
          ∫ ω, M.R (rhoHat M α N x τ (pathExt ω) n) ∂(hatLaw M α N x τ) := by sorry

end MarkdownReadjust
