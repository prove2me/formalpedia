-- Prove2me | Theorems.Thm_MWMSLagrange_ub_cost_eq_lagrangian
-- name    : MWMSLagrange.ub_cost_eq_lagrangian
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:07:06.822997+00:00
-- url     : https://prove2.me/theorems/cd0789f5-b47e-4cb6-aaeb-bd1fe9a0e03c
-- title:
--   Proof of Theorem 2, p.23: $V^{SLaBS}_{ub}=V^{\lambda^*}\le V^*$
-- statement:
--   Consider a valid MWMS instance with independent demands $D_{i,t}\in[0,\bar D]$. Let $\lambda$ be multipliers, $y_{i,t}\in[0,\bar D]$ base-stock levels and $\rho$ an allocation such that
--
--   1. the base-stock policy $(y,\rho)$ attains $V^\lambda$: its value in (3.3) equals $V^\lambda$;
--   2. $(\lambda,y,\rho)$ satisfy (3.7) (in particular $\lambda\ge0$).
--
--   Then the cost of $(y,\rho)$ in the system with unlimited warehouse inventory equals the Lagrangian bound, which is at most the optimal cost:
--
--   $$V^{SLaBS}_{ub}=V^{\lambda}\le V^* .$$
--
--   Complementary slackness makes the penalty terms of (3.3) vanish in expectation, and weak duality gives the inequality.
--
--   **Formalization Note** $V^\lambda$ appears as the real number given by the (3.3) objective of the base-stock shipments, equal to $V^\lambda$ by hypothesis 1.
--
--   Differences from the source:
--   - generalization: λ* the maximizer of V^λ over λ ≥ 0 → any λ for which (y, ρ) attains V^λ and (3.7) holds (λ ≥ 0 is part of (3.7)); reason: the step uses only complementary slackness and weak duality; at λ = λ* it is the page's statement
--   - encoding: V^{λ*} (the optimal value attained by (y*, ρ*)) → relaxedCost λ (bsShip y ρ), with the hypothesis that it equals the EReal V^λ; reason: avoids EReal subtraction; same value
--   - reading: D_{i,t} ≤ D̄ (nonnegativity not written) → each law μ_{i,t} has μ_{i,t}([0, D̄]) = 1; reason: the paper treats demand as nonnegative throughout (lost-sales dynamics; proof of Lemma 7, pp.37–38)
--   - encoding: independent, possibly non-stationary demands D_{i,t} → product measure ⊗_{i,t} μ_{i,t} on ℝ^{[N]×[T]}, D_{i,t}(ω) = ω(i,t); reason: the product of the marginals is the joint law of independent variables
--   - encoding: non-anticipating policies (y^π, ρ^π) with constraints on each sample path → measurable, non-anticipating, nonnegative shipment rules z_{i,j,t}(ω), zero off the network, constraints on every ω; reason: z = ρ(y − I) and ρ = z/Σ_j z translate between the forms; paths outside [0, D̄]^{N×T} carry no mass; the rule is deterministic and may read the whole past demand path, which gives the same infimum as randomized or state-based policies (a randomized policy is a mixture of deterministic ones; the problem is a finite-horizon MDP with state (I, R))
--   - encoding: V^λ = min of (3.3) → EReal infimum of the (3.3) objective over relaxed policies with integrable shipments; reason: V^λ can be −∞; the expectations in (3.3) presuppose integrability
--   - encoding: V* = min_{π∈Π} of (2.1) → real infimum over feasible policies; reason: the set is nonempty and bounded below (proved in the verification file); attainment is not used
-- source:
--   Miao, Jasin, Chao, Asymptotically Optimal Lagrangian Policies for Multi-Warehouse, Multi-Store Systems with Lost Sales, SSRN 3552995 (manuscript, sha256 1146a7f8…), proof of Theorem 2, p.23 ("V^SLaBS_ub = V^λ* ≤ V*"); paragraph after Lemma 5, p.21

import Mathlib
import Definitions.Def_MWMSLagrange_Instance
import Definitions.Def_MWMSLagrange_Instance_Valid
import Definitions.Def_MWMSLagrange_Vstar
import Definitions.Def_MWMSLagrange_Vlam
import Definitions.Def_MWMSLagrange_IsAllocation
import Definitions.Def_MWMSLagrange_bsShip
import Definitions.Def_MWMSLagrange_ubCost
import Definitions.Def_MWMSLagrange_CompSlack

open MeasureTheory

namespace MWMSLagrange

/-- Miao, Jasin, Chao, SSRN 3552995 (manuscript, sha256 1146a7f8…), proof of Theorem 2, p.23:
"Consider the hypothetical system `V^SLaBS_ub`. … we have `V^SLaBS_ub = V^{λ^*} ≤ V^*`, due to
the complementary slackness in Lemma 5."

Let `λ ≥ 0`, base-stock levels `y_{i,t} ∈ [0, D̄]` and an allocation `ρ` be such that the
base-stock policy `(y, ρ)` attains `V^λ` (its relaxed cost equals `V^λ`) and `(λ, y, ρ)`
satisfy (3.7). Then the cost of `(y, ρ)` in the system with unlimited warehouse inventory equals
its relaxed cost `= V^λ`, and this is at most `V^*`.

**Formalization Note.** `V^λ` is replaced by the real number `relaxedCost λ (bsShip y ρ)`,
which equals it by hypothesis. The statement does not assume that `λ` maximizes `V^λ`. -/
theorem ub_cost_eq_lagrangian {M N T : ℕ} (I : Instance M N) (hI : I.Valid) (Dbar : ℝ)
    (hD : 0 < Dbar) (μ : Fin N → Fin T → Measure ℝ) [∀ i t, IsProbabilityMeasure (μ i t)]
    (hμ : ∀ i t, μ i t (Set.Icc 0 Dbar) = 1)
    (lam : Fin M → ℝ) (y : Fin N → Fin T → ℝ) (hy : ∀ i t, 0 ≤ y i t ∧ y i t ≤ Dbar)
    (ρ : Fin N → Fin M → ℝ) (hρ : IsAllocation I ρ)
    (hopt : ((relaxedCost I μ lam (bsShip y ρ) : ℝ) : EReal) = Vlam I μ lam)
    (hcs : CompSlack I μ lam y ρ) :
    ubCost I μ y ρ = relaxedCost I μ lam (bsShip y ρ) ∧
      relaxedCost I μ lam (bsShip y ρ) ≤ Vstar I μ := by sorry

end MWMSLagrange
