-- Prove2me | Theorems.Thm_HeilmanMax3Cut_Supplement_theorem_A_1
-- name    : HeilmanMax3Cut.Supplement.theorem_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:11:00.32014+00:00
-- url     : https://prove2.me/theorems/2cac927d-07cc-458d-a4ba-417600544566
-- title:
--   Theorem A.1 — positive-correlation Standard Simplex inequality, $0<\rho\le2/5$
-- statement:
--   Let $n\ge2$, let $0<\rho\le2/5$, and let $\Omega=(\Omega_1,\Omega_2,\Omega_3)$ be a measurable partition of $\mathbb R^n$ with $\gamma_n(\Omega_i)=1/3$ for $i=1,2,3$. Then
--
--   $$Q^{(n)}_\rho(\Omega,\Omega)\ \le\ Q^{(2)}_\rho(\Theta,\Theta),$$
--
--   where $\Theta$ is the partition of $\mathbb R^2$ into three $120^\circ$ sectors and $Q^{(n)}_\rho(\Omega,\Omega)$ is the Gaussian noise stability of $\Omega$.
--
--   Among partitions into three sets of equal Gaussian measure, the standard simplex partition maximizes noise stability at positive correlation $\rho\le2/5$: the positive-correlation half of the Standard Simplex Conjecture for three sets, complementing Theorem 7.1.
--
--   Differences from the source:
--   - generalization: Ω a measurable partition of ℝⁿ into three disjoint sets → IsPartition: measurable cells, almost every point in exactly one cell; reason: every exact partition is one, so the statement specializes to the paper's; Q and γ do not see null sets
--   - encoding: Θ the three 120° sectors; cells i = 1, 2, 3; γ_n(Ω_i) = 1/3 → Theta = propeller 2 3 (closed sectors sharing null boundary rays); cells Fin 3 = 0, 1, 2; the measure condition in ℝ≥0∞; reason: null overlaps do not change Q; the index shift and the value type change no instance
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Theorem A.1, p.38, Eq. (134) (proof p.43)

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_HeilmanMax3Cut_Qstab
import Definitions.Def_HeilmanMax3Cut_Theta
open OAI.GaussianPropeller

namespace HeilmanMax3Cut.Supplement

/-- **Theorem A.1 (positive-correlation Standard Simplex inequality).** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Theorem A.1, p.38:
"Let `n ≥ 2`, let `0 < ρ ≤ 2/5`, and let `Ω = (Ω₁, Ω₂, Ω₃)` be a measurable partition of `ℝⁿ`
satisfying `γₙ(Ωᵢ) = 1/3` for all `1 ≤ i ≤ 3`. Then `Q_ρ^{(n)}(Ω, Ω) ≤ Q_ρ^{(2)}(Θ, Θ)`. (134)"

**Formalization Note.** As in the published Theorem 7.1 (`HeilmanMax3Cut.theorem_7_1`): `Ω` is an
`IsPartition` (measurable cells, `γₙ`-almost every point in exactly one cell), which includes every
exact measurable partition; cells are indexed by `Fin 3`; `Q` is the published `HeilmanMax3Cut.Qstab`
and `Θ` the published `HeilmanMax3Cut.Theta` (`propeller 2 3`). The measure condition is stated in
`ℝ≥0∞`. -/
theorem theorem_A_1 (n : ℕ) (hn : 2 ≤ n) (Ω : Fin 3 → Set (Space n)) (hΩ : IsPartition Ω)
    (hmeas : ∀ i, gaussian n (Ω i) = 1 / 3) (ρ : ℝ) (hρ : ρ ∈ Set.Ioc (0 : ℝ) (2 / 5)) :
    Qstab n ρ Ω Ω ≤ Qstab 2 ρ Theta Theta := by sorry

end HeilmanMax3Cut.Supplement
