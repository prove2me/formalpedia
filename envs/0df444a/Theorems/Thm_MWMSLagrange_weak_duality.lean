-- Prove2me | Theorems.Thm_MWMSLagrange_weak_duality
-- name    : MWMSLagrange.weak_duality
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:07:20.792367+00:00
-- url     : https://prove2.me/theorems/087559e4-f6bb-417b-9ebf-33c1dda75aab
-- title:
--   Weak duality: $V^\lambda\le V^*$ for every $\lambda\ge0$
-- statement:
--   Consider a valid MWMS instance with independent demands $D_{i,t}\in[0,\bar D]$, $\bar D>0$. For every vector of multipliers $\lambda\ge0$, the value of the Lagrangian relaxation problem (3.3) is a lower bound on the optimal expected cost:
--
--   $$V^\lambda\le V^* .$$
--
--   This is why the expected loss of any feasible policy $\pi$ can be bounded by $V^\pi-V^\lambda$ for a well-chosen $\lambda\ge0$.
--
--   **Formalization Note** $V^\lambda$ is an extended real; $V^*$ is the real infimum of (2.1) over feasible policies, cast to `EReal`.
--
--   Differences from the source:
--   - generalization: (2.1) requires Σ_{j∈M_i} ρ_{i,j,t} = 1, so every M_i is nonempty → stores with M_i = ∅ are allowed and receive nothing; reason: the argument does not use M_i ≠ ∅; on instances with every M_i nonempty it is the page's statement
--   - reading: D_{i,t} ≤ D̄ (nonnegativity not written) → each law μ_{i,t} has μ_{i,t}([0, D̄]) = 1; reason: the paper treats demand as nonnegative throughout (lost-sales dynamics; proof of Lemma 7, pp.37–38)
--   - encoding: independent, possibly non-stationary demands D_{i,t} → product measure ⊗_{i,t} μ_{i,t} on ℝ^{[N]×[T]}, D_{i,t}(ω) = ω(i,t); reason: the product of the marginals is the joint law of independent variables
--   - encoding: non-anticipating policies (y^π, ρ^π) with constraints on each sample path → measurable, non-anticipating, nonnegative shipment rules z_{i,j,t}(ω), zero off the network, constraints on every ω; reason: z = ρ(y − I) and ρ = z/Σ_j z translate between the forms; paths outside [0, D̄]^{N×T} carry no mass; the rule is deterministic and may read the whole past demand path, which gives the same infimum as randomized or state-based policies (a randomized policy is a mixture of deterministic ones; the problem is a finite-horizon MDP with state (I, R))
--   - encoding: V^λ = min of (3.3) → EReal infimum of the (3.3) objective over relaxed policies with integrable shipments; reason: V^λ can be −∞; the expectations in (3.3) presuppose integrability
--   - encoding: V* = min_{π∈Π} of (2.1) → real infimum over feasible policies; reason: the set is nonempty and bounded below (proved in the verification file); attainment is not used
-- source:
--   Miao, Jasin, Chao, Asymptotically Optimal Lagrangian Policies for Multi-Warehouse, Multi-Store Systems with Lost Sales, SSRN 3552995 (manuscript, sha256 1146a7f8…), p.10, paragraph after (3.3)

import Mathlib
import Definitions.Def_MWMSLagrange_Instance
import Definitions.Def_MWMSLagrange_Instance_Valid
import Definitions.Def_MWMSLagrange_Vstar
import Definitions.Def_MWMSLagrange_Vlam

open MeasureTheory

namespace MWMSLagrange

/-- Miao, Jasin, Chao, SSRN 3552995 (manuscript, sha256 1146a7f8…), p.10, after (3.3): weak
duality. "It is not difficult to see that `V^λ ≤ V^*` for any `λ ≥ 0`": for a valid MWMS
instance with independent demands `D_{i,t} ∈ [0, D̄]`, every nonnegative multiplier vector `λ`
gives a lower bound `V^λ ≤ V^*` on the optimal expected cost.

**Formalization Note.** `V^λ` is an `EReal` infimum over relaxed policies, `V^*` the real
infimum of (2.1) over feasible policies. -/
theorem weak_duality {M N T : ℕ} (I : Instance M N) (hI : I.Valid) (Dbar : ℝ) (hD : 0 < Dbar)
    (μ : Fin N → Fin T → Measure ℝ) [∀ i t, IsProbabilityMeasure (μ i t)]
    (hμ : ∀ i t, μ i t (Set.Icc 0 Dbar) = 1)
    (lam : Fin M → ℝ) (hlam : 0 ≤ lam) :
    Vlam I μ lam ≤ ((Vstar I μ : ℝ) : EReal) := by sorry

end MWMSLagrange
