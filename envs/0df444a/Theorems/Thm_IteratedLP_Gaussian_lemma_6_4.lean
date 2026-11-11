-- Prove2me | Theorems.Thm_IteratedLP_Gaussian_lemma_6_4
-- name    : IteratedLP.Gaussian.lemma_6_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:23:00.227996+00:00
-- url     : https://prove2.me/theorems/d3befd1d-caec-4b78-9c27-b7b2c04fa1b2
-- title:
--   Lemma 6.4 — the population problem has a point with $\phi_t(\omega)>d_t(\omega)$, so $V_t>0$, uniformly on compact input families
-- statement:
--   Fix $\alpha>0$ and a depth-$p$ input for round $t=p+1$ satisfying the assumptions of Section 6 (the empty history under (1.2) if $p=0$, a strict input in the sense of Definition 6.2 if $p\ge1$). Then
--   1. there is a column-feasible $\omega$ with $C_\omega\ne\emptyset$ (and $\rho_\omega^2\ge0$) such that $\phi_t(\omega)>d_t(\omega)$;
--   2. consequently $\Psi_t(\omega)>0$, and hence $V_t=\max_\omega\Psi_t(\omega)>0$;
--   3. on every compact family of such inputs (fixed depth, density and margins; product $W_2$ topology on the laws and Euclidean topology on $q$) there is $v_*>0$ such that
--   $$V_t\ge v_*\quad\text{throughout the family}.$$
--
--   Positivity of $V_t$ is what makes the state-evolution recursion of Algorithm 2 well defined in every round.
--
--   Differences from the source:
--
--   - reading: a column-feasible ω with C_ω ≠ ∅ → an admissible ω: ρ_ω² ≥ 0, the column competitor set and the row set nonempty; reason: for a column-feasible ω, ρ_ω² = ‖T(Y)‖² ≥ 0 (p. 31), so the extra clause excludes nothing; Ψ_t is defined on this domain
--   - encoding: V_t = max_ω Ψ_t(ω) with Ψ_t = −∞ off the positive branch → ⨆ over all ω of Psi in EReal (⊥ when ω is not admissible or ϕ_t < d_t); reason: the conclusion V_t > 0 does not need attainment; the supremum of an EReal family is total
--   - encoding: compact family in the product W₂ × Euclidean topology → sequential compactness for inputDist = |q − q'| + W₂ + W₂ + W₂, with W₂ on ℝ^p × ℝ^p for Lean's max product norm; reason: metric topology, so compact = sequentially compact; the max and Euclidean norms on ℝ^{2p} give the same W₂ topology
--   - encoding: an input satisfying the assumptions of Section 6 → IsSectionSixInput α κold κt S: the empty state with FirstRoundFeasible α κt at p = 0, or IsStrictInput (Definition 6.2 with κ_p > κ_t); reason: Section 6, p. 23
-- source:
--   Zhang, Li, State Evolution and Universality of Iterated Linear Programs for the Binary Perceptron, arXiv:2611.04294v1, p. 27, Lemma 6.4

import Mathlib
import Definitions.Def_IteratedLP_Gaussian_StateEvolution
import Definitions.Def_IteratedLP_Gaussian_StrictInput

open MeasureTheory ProbabilityTheory

namespace IteratedLP.Gaussian

/-- Lemma 6.4 (A feasible point with positive value, p. 27). Fix `α > 0` and a depth-`p` input
for round `t = p + 1` satisfying the assumptions of Section 6 (the empty input under (1.2) when
`p = 0`, a strict input of Definition 6.2 when `p ≥ 1`). Then there is a column-feasible `ω`
with `C_ω ≠ ∅` (and `ρ_ω² ≥ 0`) such that `ϕ_t(ω) > d_t(ω)`; consequently `Ψ_t(ω) > 0` and
`V_t = sup_ω Ψ_t(ω) > 0`. Moreover, on every compact family of such inputs (product of the `W₂`
topologies on the laws and the Euclidean topology on `q`) there is `v⋆ > 0` with `V_t ≥ v⋆`
throughout the family. -/
theorem lemma_6_4 (α : ℝ) (hα : 0 < α) (p : ℕ) (κold : Fin p → ℝ) (κt : ℝ) :
    (∀ S : PopState p, IsSectionSixInput α κold κt S →
      (∃ ω : Param p, Admissible α κt S ω ∧ rowCost α κt S ω < colWidth S ω) ∧
      (∃ ω : Param p, 0 < Psi α κt S ω) ∧ 0 < ⨆ ω : Param p, Psi α κt S ω) ∧
    (∀ F : Set (PopState p), (∀ S ∈ F, IsSectionSixInput α κold κt S) → IsCompactFamily F →
      ∃ v : ℝ, 0 < v ∧ ∀ S ∈ F, (v : EReal) ≤ ⨆ ω : Param p, Psi α κt S ω) := by sorry

end IteratedLP.Gaussian
