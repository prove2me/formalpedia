-- Prove2me | Theorems.Thm_JuHardCoreTransition_Mixing_theorem_1_10
-- name    : JuHardCoreTransition.Mixing.theorem_1_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:17:48.42109+00:00
-- url     : https://prove2.me/theorems/990e1f40-ac54-4a60-acc4-12f15c902d21
-- title:
--   Theorem 1.10 — spectral independence through criticality, with the optimal lower bound
-- statement:
--   There is an absolute constant $C>0$ such that for every $d\ge3$, every $n$-vertex graph $G$ of maximum degree at most $d$, and every $-1<\delta\le\delta_{\mathrm{up}}$, the hard-core distribution $\mu=\mu_{G,\lambda}$ at $\lambda=(1+\delta)\lambda_c(d)$ satisfies, for every feasible pinning $\tau$,
--   $$\lambda_{\max}(\Psi_{\mu^\tau})\le C\Big[1+\sqrt{\frac nd}+\frac nd\max\{\delta,0\}\Big].$$
--   For every fixed $d\ge3$ there is $c_d>0$ such that for every $n\ge d+1$ and every $0\le\delta\le\delta_{\mathrm{mix}}(d)$, some simple $n$-vertex graph $G$ of maximum degree $d$ satisfies $\lambda_{\max}(\Psi_{\mu_{G,(1+\delta)\lambda_c(d)}})\ge c_d(\sqrt n+n\delta)$.
--
--   Differences from the source:
--   - encoding: an n-vertex graph G=(V,E) → a SimpleGraph on Fin n (n labelled vertices); reason: every finite graph is isomorphic to one on Fin n and every quantity involved is isomorphism-invariant; this lets the absolute constant be stated before the graph
--   - reading: δ_mix(d), the constant of Theorem 1.4 → ∃ δmix > 0 for each d, before c_d; reason: a statement of its own cannot refer to the constant chosen in another item; δ_mix(d) is only specified as positive
--   - encoding: a feasible pinning τ and the law μ^τ → τ : Fin n → Option Bool with positive pinned mass, and condition μ τ; reason: partial assignment of positive probability
--   - encoding: λ_max(Ψ_{μ^τ}) after omitting deterministic coordinates → influenceMax: sSup of the real eigenvalues of Ψ on the coordinates with 0 < p_v < 1 (0 when none remains); reason: Ψ is similar to a symmetric matrix, so this is its largest eigenvalue; with no free coordinate the bound is vacuous in the source
-- source:
--   Ju, Liu and Yin, Fine-Grained Complexity Across the Computational Phase Transition, arXiv:2611.02702, pinned source.pdf dated 2026-11-02, SHA256 6288a2d2b0acc0256c0a8e1e8ea59eb0fbfff70c6d282c1c83eacf59cecd3678 (arXiv version suffix not supplied; unverified), Theorem 1.10, printed p.5 / PDF p.6

import Mathlib
import Definitions.Def_HiddenHardCoreColoring_Mixing_HardCore
import Definitions.Def_JuHardCoreTransition_Mixing_BooleanLaws
import Definitions.Def_JuHardCoreTransition_Mixing_GlauberHardCore

namespace JuHardCoreTransition.Mixing

open HiddenHardCoreColoring.Mixing

/-- **Theorem 1.10 (Spectral independence through criticality)** (printed p.5 / PDF p.6).
(1) There is an absolute `C > 0` such that for every `d ≥ 3`, every `n`-vertex graph `G` of maximum
degree at most `d` and every `−1 < δ ≤ δ_up`, the hard-core law `μ = μ_{G,λ}` at
`λ = (1 + δ)λ_c(d)` satisfies, for every feasible pinning `τ`,
`λ_max(Ψ_{μ^τ}) ≤ C[1 + √(n/d) + (n/d) max{δ, 0}]`.
(2) For every fixed `d ≥ 3` there is `c_d > 0` such that for every `n ≥ d + 1` and every
`0 ≤ δ ≤ δ_mix(d)`, some simple `n`-vertex graph `G` of maximum degree `d` satisfies
`λ_max(Ψ_{μ_{G,(1+δ)λ_c(d)}}) ≥ c_d(√n + nδ)`. (`δ_mix(d)` is the positive constant of
Theorem 1.4; here it is introduced existentially.) -/
theorem theorem_1_10 :
    (∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 3 ≤ d → ∀ n : ℕ, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v, G.degree v ≤ d) → ∀ δ : ℝ, -1 < δ → δ ≤ deltaUp →
        ∀ τ : Pinning (Fin n), IsFeasiblePinning (hcSetLaw G ((1 + δ) * lamCrit d)) τ →
          influenceMax (condition (hcSetLaw G ((1 + δ) * lamCrit d)) τ) ≤
            C * (1 + Real.sqrt ((n : ℝ) / d) + (n : ℝ) / d * max δ 0)) ∧
    (∀ d : ℕ, 3 ≤ d → ∃ δmix : ℝ, 0 < δmix ∧ ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, d + 1 ≤ n → ∀ δ : ℝ, 0 ≤ δ → δ ≤ δmix →
        ∃ G : SimpleGraph (Fin n), ∃ _ : DecidableRel G.Adj, G.maxDegree = d ∧
          c * (Real.sqrt n + (n : ℝ) * δ) ≤ influenceMax (hcSetLaw G ((1 + δ) * lamCrit d))) := by sorry

end JuHardCoreTransition.Mixing
