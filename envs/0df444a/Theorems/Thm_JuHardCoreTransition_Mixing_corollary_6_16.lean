-- Prove2me | Theorems.Thm_JuHardCoreTransition_Mixing_corollary_6_16
-- name    : JuHardCoreTransition.Mixing.corollary_6_16
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:17:30.39707+00:00
-- url     : https://prove2.me/theorems/44833730-4b30-407b-95db-592496de0bb0
-- title:
--   Corollary 6.16 — joint lower bounds at every size
-- statement:
--   After decreasing $\delta_{\mathrm{mix}}(d)$ if necessary, there is an absolute constant $c>0$ such that for every fixed $d\ge3$ there are constants $a_d,b_d>0$ with the following property. For every $n\ge d+1$ and every $0\le\delta\le\delta_{\mathrm{mix}}(d)$ there is a simple $n$-vertex graph $G$ of maximum degree $d$ such that, at fugacity $(1+\delta)\lambda_c(d)$,
--   $$\min\{t^G_{\mathrm{rel}},t^G_{\mathrm{mix}}(1/4)\}\ge a_dn^{3/2}\exp\Big\{\frac{cn\delta^2}d\Big\},\qquad \lambda_{\max}(\Psi_{\mu_G})\ge b_d(\sqrt n+n\delta).$$
--   For even $n\ge2d$ the graph may be chosen $d$-regular and bipartite.
--
--   Differences from the source:
--   - encoding: after decreasing δ_mix(d) if necessary → ∃ δmix > 0 for each d (after the absolute c); reason: δ_mix(d) is a positive constant depending on d
--   - encoding: for even n ≥ 2d the graph may be chosen d-regular and bipartite → the same witness G is d-regular and 2-colourable whenever n is even and n ≥ 2d; reason: both bounds are properties of the chosen graph, so this is equivalent
--   - encoding: an n-vertex graph G=(V,E) → a SimpleGraph on Fin n (n labelled vertices); reason: every finite graph is isomorphic to one on Fin n and every quantity involved is isomorphism-invariant; this lets the absolute constant be stated before the graph
--   - encoding: t_rel = 1/(1−θ₂), t_mix from the worst initial state → trelG = 1/gap and tmixG = tmix of the published heat-bath kernel hcP at constant activity; reason: the published gap counts eigenvalue 1 with multiplicity; the chain is irreducible, so 1 − gap is θ₂
-- source:
--   Ju, Liu and Yin, Fine-Grained Complexity Across the Computational Phase Transition, arXiv:2611.02702, pinned source.pdf dated 2026-11-02, SHA256 6288a2d2b0acc0256c0a8e1e8ea59eb0fbfff70c6d282c1c83eacf59cecd3678 (arXiv version suffix not supplied; unverified), Corollary 6.16, printed p.55 / PDF p.56

import Mathlib
import Definitions.Def_HiddenHardCoreColoring_Mixing_HardCore
import Definitions.Def_JuHardCoreTransition_Mixing_BooleanLaws
import Definitions.Def_JuHardCoreTransition_Mixing_GlauberHardCore

namespace JuHardCoreTransition.Mixing

open HiddenHardCoreColoring.Mixing

/-- **Corollary 6.16 (Lower bounds at every size)** (printed p.55 / PDF p.56). After decreasing
`δ_mix(d)` if necessary, there is an absolute `c > 0` such that for every fixed `d ≥ 3` there are
`a_d, b_d > 0` with the following property. For every `n ≥ d + 1` and every real
`0 ≤ δ ≤ δ_mix(d)` there is a simple `n`-vertex graph `G` of maximum degree `d` such that, at
fugacity `(1 + δ)λ_c(d)`,
`min{t_rel^G, t_mix^G(1/4)} ≥ a_d n^{3/2} exp(c n δ²/d)` and `λ_max(Ψ_{μ_G}) ≥ b_d(√n + nδ)`.
For even `n ≥ 2d` the graph may be chosen `d`-regular and bipartite. -/
theorem corollary_6_16 :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 3 ≤ d → ∃ δmix : ℝ, 0 < δmix ∧ ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∀ n : ℕ, d + 1 ≤ n → ∀ δ : ℝ, 0 ≤ δ → δ ≤ δmix →
        ∃ G : SimpleGraph (Fin n), ∃ _ : DecidableRel G.Adj, G.maxDegree = d ∧
          a * (n : ℝ) ^ (3 / 2 : ℝ) * Real.exp (c * (n : ℝ) * δ ^ 2 / d) ≤
            min (trelG G ((1 + δ) * lamCrit d)) (tmixG G ((1 + δ) * lamCrit d) (1 / 4) : ℝ) ∧
          b * (Real.sqrt n + (n : ℝ) * δ) ≤ influenceMax (hcSetLaw G ((1 + δ) * lamCrit d)) ∧
          (Even n → 2 * d ≤ n → G.IsRegularOfDegree d ∧ G.Colorable 2) := by sorry

end JuHardCoreTransition.Mixing
