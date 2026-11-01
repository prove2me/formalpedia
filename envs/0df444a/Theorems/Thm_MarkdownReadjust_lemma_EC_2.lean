-- Prove2me | Theorems.Thm_MarkdownReadjust_lemma_EC_2
-- name    : MarkdownReadjust.lemma_EC_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:16:41.198389+00:00
-- url     : https://prove2.me/theorems/4204dacc-57b3-46b8-9053-62ab6cd01a4e
-- title:
--   Lemma EC.2 — inventory balancing on $\mathcal G$ (corrected: identity needs $\rho^d=x_0/(\lambda T)$)
-- statement:
--   In the setting of Theorem 4, on the good event $\mathcal G$, the inventory just before the last update time satisfies
--
--   $$
--   X_{t_N-}=x_0-\sum_{n=0}^{N-1}\hat S_n=\big(x_0-\lambda T\rho^d\big)+\lambda T(x_0+1)^{-\frac N{N+2}}\,\hat\rho_N ,
--   $$
--
--   with $x_0-\lambda T\rho^d\ge0$ and $\lambda T(x_0+1)^{-\frac N{N+2}}\hat\rho_N>0$. In particular $X_{t_N-}>0$: on $\mathcal G$ the seller does not run out of inventory before $t_N$.
--
--   The printed lemma states $X_{t_N-}=\lambda T(x_0+1)^{-N/(N+2)}\hat\rho_N$; that identity holds exactly when $\rho^d=x_0/(\lambda T)$, i.e. $x_0\le\lambda T\rho^*$.
--
--   Differences from the source:
--   - correction: x₀ − Σ_{n=0}^{N−1} Ŝₙ = λT(x₀+1)^{−N/(N+2)} ρ̂_N > 0 → x₀ − Σ_{n<N} Ŝₙ = (x₀ − λTρᵈ) + λT(x₀+1)^{−N/(N+2)} ρ̂_N, with x₀ − λTρᵈ ≥ 0 and the last term > 0; reason: the proof (p.ec19) uses x₀ = λTρᵈ, false when x₀ > λTρ*; counterexample: F̄(p) = 1 − p on [0,1] (ρ* = 1/2), λ = T = x₀ = 1, k-th problem: ρᵈ = 1/2 and on 𝒢 the printed sides differ by k/2 > 0; the printed conclusion X_{t_N−} > 0 is kept
--   - generalization: valuation c.d.f. F with a density f whose derivative f′ is supported on [0,V), A1–A3 → F̄ continuous and strictly decreasing on [0,V] with F̄(0)=1, F̄(V)=0, plus A2 for R(ρ)=ρF̄⁻¹(ρ) on [0,1], |R| ≤ C on [0,1], and A3's twice differentiability with |R′|, |R″| ≤ C on the open interval (0,1) only; reason: the results use F̄ only through these properties (A1 follows from continuity at V); every model of the paper satisfies them, and nothing is required of R′, R″ at the endpoints ρ = 0, 1
--   - encoding: conditional on 𝒢 → for every path ω ∈ 𝒢; reason: the claim is a pathwise identity on the event
--   - generalization: the k-th problem of the asymptotic setting (k suppressed, p.9) → every instance (x₀, T) satisfying InSetting (x₀ ≥ 1, T > 0, N ≥ 1, α > 1/2, the N condition, ρᵈ > η₀, λT > 1); reason: each k-th problem satisfying the setting is such an instance
-- source:
--   Chen, Jasin, Simple monotonic readjustment policies with applications to markdown pricing and pricing in the presence of strategic customers, SSRN 3740871 (2023-10-09), Lemma EC.2, p.ec14 (proof p.ec19)

import Mathlib
import Definitions.Def_MarkdownReadjust_Model
import Definitions.Def_MarkdownReadjust_rhoD
import Definitions.Def_MarkdownReadjust_seqPoissonLaw
import Definitions.Def_MarkdownReadjust_hatLaw
import Definitions.Def_MarkdownReadjust_goodEvent
import Definitions.Def_MarkdownReadjust_InSetting

namespace MarkdownReadjust

/-- **Lemma EC.2 (Inventory balancing), p.ec14** (Chen–Jasin, SSRN 3740871), corrected. In the
setting of Theorem 4, conditional on the good event `𝒢`,
`X_{t_N−} = x₀ − Σ_{n=0}^{N−1} Ŝₙ = (x₀ − λTρᵈ) + λT(x₀+1)^{−N/(N+2)} ρ̂_N`,
with `x₀ − λTρᵈ ≥ 0` and `λT(x₀+1)^{−N/(N+2)} ρ̂_N > 0`; hence `X_{t_N−} > 0`.

**Formalization Note.** The printed identity `x₀ − Σ_{n<N} Ŝₙ = λT(x₀+1)^{−N/(N+2)} ρ̂_N` holds
only when `ρᵈ = x₀/(λT)`; its proof uses `x₀ = λTρᵈ`. When `x₀ > λTρ*` (so `ρᵈ = ρ*`) the two
sides differ by `x₀ − λTρᵈ > 0`; the extra term is added. The printed conclusion `X_{t_N−} > 0`
still follows. "Conditional on 𝒢" is read pathwise. -/
theorem lemma_EC_2 (M : Model) (α : ℝ) (N x : ℕ) (τ : ℝ) (h : InSetting M α N x τ) :
    ∀ ω ∈ goodEvent M α N x τ,
      (x : ℝ) - ∑ n ∈ Finset.range N, (pathExt ω n : ℝ)
          = ((x : ℝ) - M.lam * τ * rhoD M x τ)
            + M.lam * τ * ((x : ℝ) + 1) ^ (-(N : ℝ) / ((N : ℝ) + 2))
              * rhoHat M α N x τ (pathExt ω) N ∧
        0 ≤ (x : ℝ) - M.lam * τ * rhoD M x τ ∧
        0 < M.lam * τ * ((x : ℝ) + 1) ^ (-(N : ℝ) / ((N : ℝ) + 2))
              * rhoHat M α N x τ (pathExt ω) N := by sorry

end MarkdownReadjust
