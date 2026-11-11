-- Prove2me | Theorems.Thm_JuHardCoreTransition_Mixing_theorem_2_4
-- name    : JuHardCoreTransition.Mixing.theorem_2_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:17:32.424628+00:00
-- url     : https://prove2.me/theorems/f8629768-703f-450e-b28f-deddb6cc5a72
-- title:
--   Theorem 2.4 — near-critical Glauber mixing
-- statement:
--   There is an absolute constant $C>0$ such that, for every $n$-vertex simple graph $G$ with maximum degree $d=\Delta(G)\ge3$, every $0\le\delta\le\delta_{\mathrm{up}}$ and $0<\eta<1/4$, the Glauber dynamics for the hard-core distribution $\mu_{G,\lambda}$, $\lambda=(1+\delta)\lambda_c(d)$, has mixing time
--   $$t_{\mathrm{mix}}(\eta)\le Cn\Big(\frac nd\Big)^{1+\frac1{d-2}}\exp\Big\{\frac{Cn\delta^2}d\Big\}\Big[\log^2n+\log\frac1\eta\Big].$$
--
--   Differences from the source:
--   - encoding: an n-vertex graph G=(V,E) → a SimpleGraph on Fin n (n labelled vertices); reason: every finite graph is isomorphic to one on Fin n and every quantity involved is isomorphism-invariant; this lets the absolute constant be stated before the graph
--   - encoding: log² n → (log n)²; reason: standard notation
--   - encoding: t_rel = 1/(1−θ₂), t_mix from the worst initial state → trelG = 1/gap and tmixG = tmix of the published heat-bath kernel hcP at constant activity; reason: the published gap counts eigenvalue 1 with multiplicity; the chain is irreducible, so 1 − gap is θ₂
-- source:
--   Ju, Liu and Yin, Fine-Grained Complexity Across the Computational Phase Transition, arXiv:2611.02702, pinned source.pdf dated 2026-11-02, SHA256 6288a2d2b0acc0256c0a8e1e8ea59eb0fbfff70c6d282c1c83eacf59cecd3678 (arXiv version suffix not supplied; unverified), Theorem 2.4, printed p.10 / PDF p.11

import Mathlib
import Definitions.Def_HiddenHardCoreColoring_Mixing_HardCore
import Definitions.Def_JuHardCoreTransition_Mixing_GlauberHardCore

namespace JuHardCoreTransition.Mixing

open HiddenHardCoreColoring.Mixing

/-- **Theorem 2.4 (Near-critical Glauber mixing)** (printed p.10 / PDF p.11). There is an
absolute `C > 0` such that for every `n`-vertex simple graph `G` with maximum degree
`d = Δ(G) ≥ 3`, every `0 ≤ δ ≤ δ_up` and every `0 < η < 1/4`, the Glauber dynamics for `μ_{G,λ}`,
`λ = (1 + δ)λ_c(d)`, has
`t_mix(η) ≤ C n (n/d)^{1 + 1/(d−2)} exp(Cnδ²/d) [log² n + log(1/η)]`.
(The vertex set of an `n`-vertex graph is `Fin n`; `log² n = (log n)²`.) -/
theorem theorem_2_4 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      3 ≤ G.maxDegree → ∀ δ : ℝ, 0 ≤ δ → δ ≤ deltaUp → ∀ η : ℝ, 0 < η → η < 1 / 4 →
        (tmixG G ((1 + δ) * lamCrit G.maxDegree) η : ℝ) ≤
          C * n * ((n : ℝ) / G.maxDegree) ^ (1 + 1 / ((G.maxDegree : ℝ) - 2)) *
            Real.exp (C * (n : ℝ) * δ ^ 2 / G.maxDegree) *
            (Real.log n ^ 2 + Real.log (1 / η)) := by sorry

end JuHardCoreTransition.Mixing
