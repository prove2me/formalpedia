-- Prove2me | Theorems.Thm_NegativeDP_EssFinite_Supplement_theorem93
-- name    : NegativeDP.EssFinite.Supplement.theorem93
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:04:36.527174+00:00
-- url     : https://prove2.me/theorems/884f1954-2a45-4e09-8ef9-0943b3e8bcef
-- title:
--   Theorem 9.3 (D) — switching to whichever of σ, τ has the better continuation return beats both
-- statement:
--   Discounted case. Let $\sigma$ and $\tau$ be policies (randomized, depending on the whole history), and define $\pi$ by
--
--   $$
--   \pi_n=\begin{cases}\sigma_n&\text{if }(s_1,a_1,\dots,a_{n-1},s_n)\in B_n,\\ \tau_n&\text{if }(s_1,a_1,\dots,a_{n-1},s_n)\in B_n^c,\end{cases}
--   $$
--
--   where $B_n=\{u_n>v_n\}$ and $u_n=\sum_{j=n}^\infty\beta^{j-1}\sigma_nq\cdots\sigma_jqr$, $v_n=\sum_{j=n}^\infty\beta^{j-1}\tau_nq\cdots\tau_jqr$ are the continuation returns at the history $(s_1,a_1,\dots,s_n)$. Then such a policy $\pi$ exists and
--
--   $$
--   I(\pi)\ge\max(I(\sigma),I(\tau)).
--   $$
--
--   The negative case of this theorem is the published item `NegativeDP.Switching.theorem93`; together with this item it covers the whole source theorem. The theorem is the improvement routine of §9.
--
--   **Formalization Note** `Disc.IsSwitch P σ τ π` says that at every Lean decision `n` and history `h`, `π.κ n h` is `σ.κ n h` if `contReturn τ < contReturn σ` and `τ.κ n h` otherwise; `Disc.contReturn` keeps the printed factor $\beta^{j-1}$ (at Lean decision $n$, term $k$ has `P.β ^ (n + k)`), so for $\beta=0$ every $B_n$ with $n\ge2$ is empty. The existence conjunct asserts that the switching kernels form a policy (the sets $B_n$ are Borel).
--
--   Differences from the source:
--   - encoding: one theorem for the cases D, N → the cases not yet published (D); the negative case is the published NegativeDP.Switching.theorem93; reason: the negative case is already published and immutable; the two items together state the whole theorem
--   - reading: define π by … (π is a policy) → a conjunct asserting that a plan with the switching kernels exists, and the inequality for every such plan; reason: the paper takes for granted that the sets Bₙ are Borel, so that π is a policy; the existence conjunct states it
--   - encoding: stages numbered from 1, β^{j−1} weights → stages numbered from 0, weight P.β ^ j; reason: index shift only; Lean stage j is the paper's stage j + 1
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966) 871–890, DOI 10.1214/aoms/1177699369, p. 888, Theorem 9.3

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_DiscountedDP_Stationary_Operators
import Definitions.Def_NegativeDP_EssFinite_Supplement_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open DiscountedDP.Stationary (Hist Plan MarkovPlan Problem I T Ta U optReturn IsOptimal IsBM supNorm stationary IsGenerated IsGeneratedPlan)

namespace NegativeDP.EssFinite.Supplement

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Theorem 9.3 (p. 888), discounted case: for any policies `σ`, `τ` (randomized, depending on
the whole history) the switching policy `π` (use `σₙ` on `Bₙ = {uₙ > vₙ}` and `τₙ` on its
complement, `uₙ`, `vₙ` the discounted continuation returns of `σ`, `τ`) exists, and
`I(π) ≥ max (I(σ), I(τ))`. The negative case is the published `NegativeDP.Switching.theorem93`. -/
theorem theorem93 (P : Problem S A) (σ τ : Plan (S := S) (A := A)) :
    (∃ π : Plan (S := S) (A := A), Disc.IsSwitch P σ τ π) ∧
    ∀ π : Plan (S := S) (A := A), Disc.IsSwitch P σ τ π →
      ∀ s, max (I P σ s) (I P τ s) ≤ I P π s := by sorry

end NegativeDP.EssFinite.Supplement
