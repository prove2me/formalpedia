-- Prove2me | Theorems.Thm_JuHardCoreTransition_Mixing_theorem_6_15
-- name    : JuHardCoreTransition.Mixing.theorem_6_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:17:40.243093+00:00
-- url     : https://prove2.me/theorems/09eadfea-41ed-464d-87a6-2333fc8caa34
-- title:
--   Theorem 6.15 — relaxation and spectral-independence lower bounds from one gadget
-- statement:
--   For every fixed $d\ge3$ there are constants $c_d,C_d,t_d>0$ and $n_d$ such that for every $n\ge n_d$ divisible by four and every $0\le t\le t_d$ there is a simple $d$-regular bipartite graph $G$ on $n$ vertices such that, at fugacity $\lambda=\lambda_c(d)e^t$,
--   $$t^G_{\mathrm{rel}}\ge c_d\frac{n^{3/2}}{\sqrt{1+nt^2}}\exp\Big\{n\Big[\frac{3(d-2)}{4d^2}t^2-C_dt^3\Big]\Big\},\qquad \lambda_{\max}(\Psi_{\mu_{G,\lambda}})\ge c_d(\sqrt n+nt).$$
--
--   Differences from the source:
--   - encoding: an n-vertex graph G=(V,E) → a SimpleGraph on Fin n (n labelled vertices); reason: every finite graph is isomorphic to one on Fin n and every quantity involved is isomorphism-invariant; this lets the absolute constant be stated before the graph
--   - encoding: bipartite → G.Colorable 2; reason: standard
--   - encoding: t_rel = 1/(1−θ₂), t_mix from the worst initial state → trelG = 1/gap and tmixG = tmix of the published heat-bath kernel hcP at constant activity; reason: the published gap counts eigenvalue 1 with multiplicity; the chain is irreducible, so 1 − gap is θ₂
-- source:
--   Ju, Liu and Yin, Fine-Grained Complexity Across the Computational Phase Transition, arXiv:2611.02702, pinned source.pdf dated 2026-11-02, SHA256 6288a2d2b0acc0256c0a8e1e8ea59eb0fbfff70c6d282c1c83eacf59cecd3678 (arXiv version suffix not supplied; unverified), Theorem 6.15, printed p.52 / PDF p.53

import Mathlib
import Definitions.Def_HiddenHardCoreColoring_Mixing_HardCore
import Definitions.Def_JuHardCoreTransition_Mixing_BooleanLaws
import Definitions.Def_JuHardCoreTransition_Mixing_GlauberHardCore

namespace JuHardCoreTransition.Mixing

open HiddenHardCoreColoring.Mixing

/-- **Theorem 6.15 (Lower bounds from one gadget)** (printed pp.52–53 / PDF pp.53–54). For every
fixed `d ≥ 3` there are `c_d, C_d, t_d > 0` and `n_d` such that for every `n ≥ n_d` divisible by
four and every real `0 ≤ t ≤ t_d` there is a simple `d`-regular bipartite graph `G` on `n`
vertices such that, at fugacity `λ = λ_c(d) e^t`,
`t_rel^G ≥ c_d n^{3/2}/√(1 + nt²) · exp(n[3(d−2)t²/(4d²) − C_d t³])` (6.11) and
`λ_max(Ψ_{μ_{G,λ}}) ≥ c_d(√n + nt)` (6.12). -/
theorem theorem_6_15 (d : ℕ) (hd : 3 ≤ d) :
    ∃ c C td : ℝ, 0 < c ∧ 0 < C ∧ 0 < td ∧ ∃ nd : ℕ, ∀ n : ℕ, nd ≤ n → 4 ∣ n →
      ∀ t : ℝ, 0 ≤ t → t ≤ td →
        ∃ G : SimpleGraph (Fin n), ∃ _ : DecidableRel G.Adj,
          G.IsRegularOfDegree d ∧ G.Colorable 2 ∧
          c * (n : ℝ) ^ (3 / 2 : ℝ) / Real.sqrt (1 + (n : ℝ) * t ^ 2) *
              Real.exp ((n : ℝ) * (3 * ((d : ℝ) - 2) / (4 * (d : ℝ) ^ 2) * t ^ 2 - C * t ^ 3)) ≤
            trelG G (lamCrit d * Real.exp t) ∧
          c * (Real.sqrt n + (n : ℝ) * t) ≤ influenceMax (hcSetLaw G (lamCrit d * Real.exp t)) := by sorry

end JuHardCoreTransition.Mixing
