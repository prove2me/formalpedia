-- Prove2me | Theorems.Thm_MWMSLagrange_theorem_2
-- name    : MWMSLagrange.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:07:06.695353+00:00
-- url     : https://prove2.me/theorems/6464558e-8db3-4dfa-a09d-d7077cd3018b
-- title:
--   Theorem 2: SLaBS loss $\le V^{SLaBS}-V^{\lambda^*}=O(\sqrt{\min\{M,N\}TN\log(TN)})$ (corrected: constant depends on $\bar D$ and a bound $B$ on all costs)
-- statement:
--   Fix a demand bound $\bar D>0$ and a cost bound $B$. There is a constant $K$, depending only on $\bar D$ and $B$, with the following property. Let $M$ warehouses, $N\ge1$ stores and $T\ge1$ periods be given, together with
--
--   1. a valid MWMS instance (network, inventories $C_j\ge0$, costs $h_i,b_i,c_{i,j}\ge0$, $w_j$) with $h_i,b_i,c_{i,j},|w_j|\le B$;
--   2. independent demands $D_{i,t}$ with laws on $[0,\bar D]$;
--   3. a maximizer $\lambda^*$ of $V^\lambda$ over $\lambda\ge0$;
--   4. base-stock levels $y^*_{i,t}\in[0,\bar D]$ and an allocation $\rho^*$ that are optimal for $V^{\lambda^*}$ and satisfy (3.7);
--   5. a run $\pi$ of SLaBS with these inputs, with any split of a warehouse's last units.
--
--   Then
--
--   $$L^{SLaBS}=V^{\pi}-V^*\le V^{\pi}-V^{\lambda^*}\qquad\text{and}\qquad V^{\pi}-V^{\lambda^*}\le K\sqrt{\min\{M,N\}\,T\,N\log(TN)} .$$
--
--   The expected loss of SLaBS grows sublinearly in both the horizon $T$ and the number of stores $N$, so the policy is asymptotically optimal.
--
--   **Formalization Note** $V^{\lambda^*}$ is written as the real (3.3) objective of the base-stock shipments, which equals the extended-real $V^{\lambda^*}$ by hypothesis. $K$ is chosen before $M$, $N$, $T$ and the instance.
--
--   Differences from the source:
--   - correction: O(√(min{M,N}TN log(TN))) with the proof's constant b̄D̄2√2 and additive b̄D̄ (p.25), depending on b̄ = max_i b_i and D̄ only → ∃ K depending on D̄ and a bound B ≥ h_i, b_i, c_{i,j}, |w_j|, chosen before M, N, T and the instance; reason: counterexample satisfying every assumption: M = N = 1, T = 2, h = b = c = 0, w = W > 0, D̄ = 1, D_{1,1}, D_{1,2} i.i.d. Bernoulli(1/2), C = 3/4, λ* = W, y* = 1/2, ρ* = 1 gives V^{λ*} = V* = 0 and loss W/8, while b̄ = 0
--   - reading: O(√(min{M,N}TN log(TN))) → ≤ K·√(min{M,N}·T·N·log(TN)) for all N, T ≥ 1, including TN = 1 where log(TN) = 0; reason: the standard reading of an O(·) in M, N, T with the primitives fixed; at TN = 1 the real and uncapacitated systems coincide and the gap is 0
--   - reading: split the remaining arbitrarily to each store and stop ordering from this warehouse → every split with 0 ≤ z_{i,j,t} ≤ the request ρ*_{i,j}(y*_{i,t} − I_{i,t})^+ and total equal to the remainder; requests use the actual on-hand inventory; the rule holds on every ω and is measurable and non-anticipating like every policy; reason: the page leaves the split arbitrary; the bound is claimed for all of them; paths outside [0, D̄]^{N×T} carry no mass
--   - reading: y*, ρ* of Algorithm 1 step 2, whose existence the paper takes from Lemma 5 → quantified as hypotheses, so the statement says nothing about an instance with no such inputs; reason: Algorithm 1 takes them as given and SLaBS is undefined without them; Lemma 5 fails in a boundary case (M = N = T = 1, h = b = c = 0, w = 1, D̄ = 1, D ≡ 1/2, C = 2, where λ* = 1 forces y* = 2 ∉ [0, D̄])
--   - reading: D_{i,t} ≤ D̄ (nonnegativity not written) → each law μ_{i,t} has μ_{i,t}([0, D̄]) = 1; reason: the paper treats demand as nonnegative throughout (lost-sales dynamics; proof of Lemma 7, pp.37–38)
--   - encoding: y*, ρ* optimal solutions of V^{λ*}_i for each store (Algorithm 1, step 2); the value V^{λ*} → relaxedCost λ* (bsShip y* ρ*) = V^{λ*} (EReal), and V^{λ*} written as that real number; reason: V^λ = Σ_j (w_j − λ_j)C_j + Σ_i V^λ_i (p.10), so per-store optimality is optimality for V^λ; avoids EReal subtraction
--   - encoding: M ≥ 1 and every M_i nonempty → not assumed separately; reason: implied by N ≥ 1 and Σ_{j∈M_i} ρ*_{i,j} = 1; no instance is added or removed
--   - encoding: independent, possibly non-stationary demands D_{i,t} → product measure ⊗_{i,t} μ_{i,t} on ℝ^{[N]×[T]}, D_{i,t}(ω) = ω(i,t); reason: the product of the marginals is the joint law of independent variables
--   - encoding: non-anticipating policies (y^π, ρ^π) with constraints on each sample path → measurable, non-anticipating, nonnegative shipment rules z_{i,j,t}(ω), zero off the network, constraints on every ω; reason: z = ρ(y − I) and ρ = z/Σ_j z translate between the forms; paths outside [0, D̄]^{N×T} carry no mass; the rule is deterministic and may read the whole past demand path, which gives the same infimum as randomized or state-based policies (a randomized policy is a mixture of deterministic ones; the problem is a finite-horizon MDP with state (I, R))
--   - encoding: V^λ = min of (3.3) → EReal infimum of the (3.3) objective over relaxed policies with integrable shipments; reason: V^λ can be −∞; the expectations in (3.3) presuppose integrability
--   - encoding: V* = min_{π∈Π} of (2.1) → real infimum over feasible policies; reason: the set is nonempty and bounded below (proved in the verification file); attainment is not used
-- source:
--   Miao, Jasin, Chao, Asymptotically Optimal Lagrangian Policies for Multi-Warehouse, Multi-Store Systems with Lost Sales, SSRN 3552995 (manuscript, sha256 1146a7f8…), Theorem 2, p.13; proof pp.23–25

import Mathlib
import Definitions.Def_MWMSLagrange_Instance
import Definitions.Def_MWMSLagrange_Instance_Valid
import Definitions.Def_MWMSLagrange_Instance_CostBound
import Definitions.Def_MWMSLagrange_FeasiblePolicy
import Definitions.Def_MWMSLagrange_cost
import Definitions.Def_MWMSLagrange_Vstar
import Definitions.Def_MWMSLagrange_relaxedCost
import Definitions.Def_MWMSLagrange_Vlam
import Definitions.Def_MWMSLagrange_IsAllocation
import Definitions.Def_MWMSLagrange_bsShip
import Definitions.Def_MWMSLagrange_CompSlack
import Definitions.Def_MWMSLagrange_IsSLaBSRun

open MeasureTheory

namespace MWMSLagrange

/-- Miao, Jasin, Chao, SSRN 3552995 (manuscript, sha256 1146a7f8…), Theorem 2, p.13: "The
expected loss of SLaBS can be bounded as follows:
`L^SLaBS ≤ V^SLaBS − V^{λ^*} = O(√(min{M, N} T N log(TN)))`."

For every demand bound `D̄ > 0` and cost bound `B` there is a constant `K` such that for all
`M` warehouses, `N ≥ 1` stores and `T ≥ 1` periods, every valid instance whose costs
`h_i, b_i, c_{i,j}, |w_j|` are at most `B`, all independent demands `D_{i,t} ∈ [0, D̄]`, every
maximizer `λ^*` of `V^λ` over `λ ≥ 0`, all base-stock levels `y^*_{i,t} ∈ [0, D̄]` and allocations
`ρ^*` that are optimal for `V^{λ^*}` and satisfy (3.7), and every run `π` of SLaBS with these
inputs (any split of a warehouse's last units):
`V^π − V^* ≤ V^π − V^{λ^*}` and `V^π − V^{λ^*} ≤ K √(min{M, N} T N log(TN))`.

**Formalization Note.** `V^{λ^*}` is written as the real number `relaxedCost λ^* (bsShip y^* ρ^*)`,
which equals the `EReal` value `V^{λ^*}` by hypothesis. `K` is chosen before `M, N, T` and the
instance and depends only on `D̄` and `B` (correction of the paper's constant, which uses
`b̄ = max_i b_i` and `D̄` only and is false). -/
theorem theorem_2 (Dbar B : ℝ) (hD : 0 < Dbar) :
    ∃ K : ℝ, ∀ (M N T : ℕ), 0 < N → 0 < T →
      ∀ (I : Instance M N), I.Valid → I.CostBound B →
      ∀ (μ : Fin N → Fin T → Measure ℝ) [∀ i t, IsProbabilityMeasure (μ i t)],
        (∀ i t, μ i t (Set.Icc 0 Dbar) = 1) →
      ∀ (lam : Fin M → ℝ), IsMaxOn (fun l => Vlam I μ l) {l | 0 ≤ l} lam →
      ∀ (y : Fin N → Fin T → ℝ), (∀ i t, 0 ≤ y i t ∧ y i t ≤ Dbar) →
      ∀ (ρ : Fin N → Fin M → ℝ), IsAllocation I ρ →
        ((relaxedCost I μ lam (bsShip y ρ) : ℝ) : EReal) = Vlam I μ lam →
        CompSlack I μ lam y ρ →
      ∀ (π : FeasiblePolicy I T), IsSLaBSRun I y ρ π →
        cost I μ π.z - Vstar I μ ≤ cost I μ π.z - relaxedCost I μ lam (bsShip y ρ) ∧
          cost I μ π.z - relaxedCost I μ lam (bsShip y ρ)
            ≤ K * Real.sqrt (((min M N : ℕ) : ℝ) * T * N * Real.log ((T : ℝ) * N)) := by sorry

end MWMSLagrange
