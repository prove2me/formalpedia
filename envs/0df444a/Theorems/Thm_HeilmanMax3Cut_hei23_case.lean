-- Prove2me | Theorems.Thm_HeilmanMax3Cut_hei23_case
-- name    : HeilmanMax3Cut.hei23_case
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:29:02.767595+00:00
-- url     : https://prove2.me/theorems/53df14ae-6f69-4578-bee1-362dc1157a8f
-- title:
--   Proof of Theorem 7.1, p.37 — the case $0<\sigma<1/43$ by [Hei23]
-- statement:
--   For every $n\ge2$, every partition $\Omega$ of $\mathbb R^n$ into three measurable sets and every $\rho\in(-1/43,0)$,
--
--   $$Q^{(n)}_\rho(\Omega,\Omega)\ \ge\ Q^{(2)}_\rho(\Theta,\Theta).$$
--
--   The paper takes this case of Theorem 7.1 ($\sigma=-\rho<1/43$) from S. Heilman, *Three Candidate Plurality is Stablest for Correlations at most 1/10*, arXiv:2306.03312.
--
--   Differences from the source:
--   - encoding: 0 < σ < 1/43 with σ = −ρ → ρ ∈ (−1/43, 0); reason: σ := −ρ (p.21)
--   - generalization: Ω (or A, B) a measurable partition of the space into three disjoint sets → IsPartition: measurable cells, almost every point in exactly one cell; reason: every exact partition is one, so the statement specializes to the paper's; Q and γ do not see null sets
--   - encoding: Θ the three 120° sectors; cells i = 1, 2, 3 → Theta = propeller 2 3 (closed sectors sharing null boundary rays); cells Fin 3 = 0, 1, 2; reason: null overlaps do not change Q; the index shift changes no instance
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Section 10, proof of Theorem 7.1, p.37 ("The case 0 < σ < 1/43 is covered by [Hei23]")

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_HeilmanMax3Cut_Qstab
import Definitions.Def_HeilmanMax3Cut_Theta
open OAI.GaussianPropeller

namespace HeilmanMax3Cut

/-- **Theorem 7.1 for `−1/43 < ρ < 0`, by [Hei23].** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Section 10, p.37: "Proof of Theorem 7.1.
Let `σ ∈ (0, 1/2]`. The case `0 < σ < 1/43` is covered by [Hei23]." Here `σ = −ρ`, and [Hei23] is
S. Heilman, *Three Candidate Plurality is Stablest for Correlations at most 1/10*,
arXiv:2306.03312.

For every `n ≥ 2`, every measurable partition `Ω` of `ℝⁿ` into three sets and every
`ρ ∈ (−1/43, 0)`: `Q_ρ^{(n)}(Ω, Ω) ≥ Q_ρ^{(2)}(Θ, Θ)`.

**Formalization Note.** Partitions are `IsPartition` (a.e.); `Θ` is `propeller 2 3`. -/
theorem hei23_case (n : ℕ) (hn : 2 ≤ n) (Ω : Fin 3 → Set (Space n)) (hΩ : IsPartition Ω)
    (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (-1 / 43 : ℝ) 0) :
    Qstab 2 ρ Theta Theta ≤ Qstab n ρ Ω Ω := by sorry

end HeilmanMax3Cut
