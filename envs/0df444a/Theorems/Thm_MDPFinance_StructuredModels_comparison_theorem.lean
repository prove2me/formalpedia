-- Prove2me | Theorems.Thm_MDPFinance_StructuredModels_comparison_theorem
-- name    : MDPFinance.StructuredModels.comparison_theorem
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T21:39:03.719839+00:00
-- url     : https://prove2.me/theorems/c11b4f6b-b01c-45e2-abc2-c561b29c0c1f
-- title:
--   Theorem 2.4.23 — comparison of Markov Decision Models under a stochastic order
-- statement:
--   Let $M$ be a Markov Decision Model with upper bounding function $b$ satisfying (SAN) with
--   $\mathrm{I\!M}_n^\diamond$, $\diamond \in \{\mathrm{st}, \mathrm{cv}, \mathrm{cx}\}$, and let
--   $\tilde M$ share the same $D_n$, $r_n$, $g_N$ as $M$, differing only in its transition kernels
--   $\tilde Q_n$. If $Q_n(\cdot \mid x,a) \leq_\diamond \tilde Q_n(\cdot \mid x,a)$ for every
--   admissible $(x,a)$ and every $n$, then $V_n \leq \tilde V_n$ for every $n = 0,\dots,N$.
--
--   **Formalization Note.** The two models are formalized as separate `MarkovDecisionModel`
--   structures with explicit equality hypotheses on `D`, `r`, `g` (the book's informal "replacing
--   $Q_n$ by $\tilde Q_n$" of an otherwise-fixed model), rather than a single structure with two
--   kernel fields, to keep the statement symmetric with `V`'s own signature. `diamond : OrderKind`
--   selects which of the three cases is in play; see the `OrderKind`/`LEDiamond`/`IMDiamond`
--   definition items.
--
--   **Formalization Note (moderation).** Both models are required to satisfy (SAN) with
--   $\mathrm{I\!M}^\diamond_n$: the book's $\tilde V_n$ are "the value functions of the Markov
--   Decision Model with transition kernels $\tilde Q_n$", and the induction $\tilde V_n = \tilde
--   T_n \tilde V_{n+1}$ on which the proof rests is their Bellman equation (Theorem 2.3.8). $V$ in
--   this mission is the Bellman recursion $T_n \cdots T_{N-1} g_N$, which under (SAN) is the value
--   function; without (SAN) for $\tilde M$ the recursion only dominates $\tilde V_n$ (Theorem
--   2.3.7a).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 38, Theorem 2.4.23

import Mathlib
import Definitions.Def_MDPFinance_StructuredModels_Model
import Definitions.Def_MDPFinance_StructuredModels_Policy
import Definitions.Def_MDPFinance_StructuredModels_Operators
import Definitions.Def_MDPFinance_StructuredModels_BoundingFunction
import Definitions.Def_MDPFinance_StructuredModels_StructureAssumption
import Definitions.Def_MDPFinance_StructuredModels_StochasticOrders
import Definitions.Def_MDPFinance_StructuredModels_ValueFunction
import Definitions.Def_MDPFinance_StructuredModels_ConvexAnalysis
import Definitions.Def_MDPFinance_StructuredModels_OrderKind

open MeasureTheory ProbabilityTheory

namespace MDPFinance.StructuredModels

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] [Preorder E]
  [AddCommGroup E] [Module ℝ E]

/-- Theorem 2.4.23 (Bäuerle–Rieder, p. 38, PDF 53). Suppose a Markov Decision Model `M` with
upper bounding function `b` is given which satisfies the Structure Assumption (SAN) with the set
`IM_n^⋄` where `⋄ ∈ {st, cv, cx}`, and `M̃` is a second Markov Decision Model with the same
`D`, `r` and `g` as `M` (only the transition kernels differ). If for all `n = 0, …, N-1`,
`Q_n(·|x,a) ≤_⋄ Q̃_n(·|x,a)` for all `(x,a) ∈ D`, then `V_n ≤ Ṽ_n` for `n = 0, …, N-1`. Both models satisfy (SAN) with `IM_n^⋄` (the book's `Ṽ_n`
are "the value functions of the Markov Decision Model with transition kernels `Q̃_n`", and the
induction `Ṽ_n = T̃_n Ṽ_{n+1}` that the proof rests on is their Bellman equation, Theorem 2.3.8);
`V` here is the Bellman recursion `T_n ⋯ T_{N-1} g_N`, which under (SAN) is the value function. -/
theorem comparison_theorem {N : ℕ} (M Mtilde : MarkovDecisionModel E A N) (b : E → ℝ)
    (cr cg αb : ℝ) (hb : IsUpperBoundingFunction M b cr cg αb)
    (hbtilde : IsUpperBoundingFunction Mtilde b cr cg αb)
    (Deltas Deltas' : ℕ → Set (E → A)) (diamond : OrderKind)
    (hSAN : StructureAssumption M (fun _ => IMDiamond b diamond) Deltas)
    (hSANtilde : StructureAssumption Mtilde (fun _ => IMDiamond b diamond) Deltas')
    (hD_eq : ∀ n < N, M.D n = Mtilde.D n) (hr_eq : ∀ n < N, M.r n = Mtilde.r n)
    (hg_eq : M.g = Mtilde.g)
    (hQ_le : ∀ n < N, ∀ xa ∈ M.D n, LEDiamond diamond (M.Q n xa) (Mtilde.Q n xa)) :
    ∀ n ≤ N, ∀ x : E, V M n x ≤ V Mtilde n x := by sorry

end MDPFinance.StructuredModels
