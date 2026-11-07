-- Prove2me | Theorems.Thm_HardCoreBochner_tmix_le_of_gap
-- name    : HardCoreBochner.tmix_le_of_gap
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:32:24.931298+00:00
-- url     : https://prove2.me/theorems/1423e7ef-6a67-4298-bf31-107fe80812ea
-- title:
--   Proof of Theorem 1.1 — gap $\delta/((1+\lambda)n)$ gives $T_{\mathrm{mix}}\le(1+\lambda)n\delta^{-1}\log(4/\mu_{\min})$
-- statement:
--   Let $G$ be a graph on $n$ vertices, $\lambda>0$, $\delta\in(0,1)$, $\mu=\mu_{G,\lambda}$ and $P_{GD}$ its Glauber dynamics. Suppose that
--   $$\gamma(P_{GD})\ge\frac{\delta}{(1+\lambda)n},\qquad\text{i.e.}\qquad \frac{\delta}{(1+\lambda)n}\,\mathrm{Var}_\mu(f)\le\langle f,(I-P_{GD})f\rangle_\mu\ \text{ for all } f.$$
--   Then
--   $$T_{\mathrm{mix}}(P_{GD})\le(1+\lambda)\,n\,\delta^{-1}\log\big(4/\mu_{\min}\big),\qquad \mu_{\min}=\min_\sigma\mu(\sigma):$$
--   from every independent set $\sigma$ there is a time $t\le(1+\lambda)n\delta^{-1}\log(4/\mu_{\min})$ with $d_{TV}\big(P^t_{GD}(\sigma,\cdot),\mu\big)<\tfrac14$.
--
--   This is the relaxation-to-mixing step of the proof of Theorem 1.1.
--
--   Differences from the source:
--   - encoding: T_mix(P) = max_σ min{t ≥ 0 : d_TV(P^t(σ,·), µ) < 1/4} ≤ B → ∀ σ, ∃ t : ℕ, t ≤ B ∧ tvDist (rowDist P t σ) µ < 1/4; reason: max_σ min{…} ≤ B holds exactly when every start has such a t; the ∃ form has no sInf of an empty set
--   - encoding: Glauber dynamics for the hard-core model on the independent sets of G → hcChain G λ = MarkovMixing.subChain (MarkovMixing.glauber (MarkovMixing.hardcoreDist G λ)) (MarkovMixing.IsHardcore G); reason: the published heat-bath chain for the published hard-core law, restricted to the independent sets; off the diagonal it is (1)
--   - encoding: γ(P_GD) ≥ δ/((1 + λ)n) → ∀ f, δ/((1 + λ)n) Var_µ(f) ≤ ⟨f, (I − glauber µ)f⟩_µ; reason: the inequality form of the spectral-gap bound; glauber µ weighted by µ is P_GD on the independent sets
-- source:
--   Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, A simple proof of rapid mixing on random regular graphs beyond uniqueness, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b6107de9702dda27883f2839093b816f7a6f9c543fcb2be0ad91ad6ad), proof of Theorem 1.1, p.4 (PDF p.4)

import Definitions.Def_mm_coupling
import Definitions.Def_mm_mcmc
import Definitions.Def_mm_mixing
import Definitions.Def_HardCoreBochner_ip
import Definitions.Def_HardCoreBochner_dirP
import Definitions.Def_HardCoreBochner_muMin
import Definitions.Def_HardCoreBochner_hcChain

namespace HardCoreBochner

open scoped BigOperators

/-- **From the spectral gap of `P_GD` to the mixing time.** Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, *A simple proof of rapid mixing on random
regular graphs beyond uniqueness*, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b…), proof of Theorem 1.1, p.4: "γ(PGD) ≥
δ/((1 + λ)n) by (4). This shows Tmix(PGD) ≤ (1 + λ)nδ^−1 log (4/µmin) where µmin = minσ µ(σ)."

Let `G` have `n` vertices, `λ > 0`, `δ ∈ (0,1)`, `µ = µ_{G,λ}`. If
`δ/((1 + λ)n) · Var_µ(f) ≤ ⟨f, (I − P_GD)f⟩_µ` for all `f`, then from every independent set `σ` some
`t ≤ (1 + λ) n δ⁻¹ log(4/µ_min)` has `d_TV(P_GD^t(σ, ·), µ) < 1/4`; that is,
`T_mix(P_GD) ≤ (1 + λ) n δ⁻¹ log(4/µ_min)`.

**Formalization Note** `T_mix(P) = max_σ min{t ≥ 0 : d_TV(P^t(σ,·), µ) < 1/4}` (p.2) is bounded by `B`
exactly when every start `σ` has a time `t ≤ B` with `d_TV < 1/4`; this is the form stated, so no
`sInf` of an empty set appears. `P_GD` on the independent sets is `hcChain G λ` (the published
`glauber` restricted by `subChain`); in the hypothesis it is `MarkovMixing.glauber µ` weighted by
`µ`, which is the same chain on the support. `d_TV` and `P^t(σ,·)` are the published `tvDist` and
`rowDist`. `µ_min` is `muMin`, the minimum over the independent sets. -/
theorem tmix_le_of_gap {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (lam δ : ℝ) (hlam : 0 < lam) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hgap : ∀ f : (V → Bool) → ℝ,
      δ / ((1 + lam) * Fintype.card V) * var (MarkovMixing.hardcoreDist G lam) f ≤
        dirP (MarkovMixing.hardcoreDist G lam)
          (MarkovMixing.glauber (MarkovMixing.hardcoreDist G lam)) f) :
    ∀ σ : {σ : V → Bool // MarkovMixing.IsHardcore G σ}, ∃ t : ℕ,
      (t : ℝ) ≤ (1 + lam) * Fintype.card V * δ⁻¹ *
          Real.log (4 / muMin (MarkovMixing.hardcoreDist G lam)) ∧
        MarkovMixing.tvDist (MarkovMixing.rowDist (hcChain G lam) t σ) (hcLaw G lam) < 1 / 4 := by sorry

end HardCoreBochner
