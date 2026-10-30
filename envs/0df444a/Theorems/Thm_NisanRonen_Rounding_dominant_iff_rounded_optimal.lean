-- Prove2me | Theorems.Thm_NisanRonen_Rounding_dominant_iff_rounded_optimal
-- name    : NisanRonen.Rounding.dominant_iff_rounded_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:29:07.347222+00:00
-- url     : https://prove2.me/theorems/c015dd5f-60ef-4528-900a-ab2f2287b43a
-- title:
--   Dominant strategies of the rounding mechanism (corrected: an equivalence, not 'same rounded value')
-- statement:
--   Let $0 < a < b$, $\delta > 0$, let $f$ be an exact solver of the rounded problem, let $t$ be a type matrix with entries in $[a,b]$, and let $\sigma = (d^i, e^i)$ be an admissible strategy of agent $i$. Then $\sigma$ is dominant if and only if, for every profile of the other agents with declarations $d^{-i} \in [a,b]^{(n-1) \times k}$, writing $d = (d^{-i}, d^i)$ and $x = x_f(d)$,
--
--   $$
--   \hat g\big(x, \mathrm{corr}^i(x, d, e^i(x))\big) \le \hat g\big(y, \mathrm{corr}^*(y, (d^{-i}, t^i))\big) \quad \text{for every allocation } y .
--   $$
--
--   That is, a strategy is dominant exactly when, against every declaration of the others, the rounded make-span of agent $i$'s corrected time vector is optimal for the rounded instance in which $i$ reports its true type. This is what "arguments similar to those in 5.1" give for the rounding mechanism.
--
--   Differences from the source:
--   - correction: the only dominant strategies declare a type with the same rounded value as t^i and execute so that the rounded corr^i equals the rounded corr* → a strategy is dominant iff against every in-box declaration of the others its rounded corrected make-span is optimal for the rounded instance with i's true type; reason: the printed claim is false: with δ = 1, a = 3, b = 5, an agent of type (3, 3) has the dominant declaration (4, 3) (rounded value differs) even under lexicographic tie-breaking (planning_numerics/search_fixed_tiebreak.py); the equivalence is what Section 5.1's argument proves
--   - encoding: agents 1, …, n and tasks 1, …, k → `Fin n` and `Fin k`, i.e. 0, …, n − 1 and 0, …, k − 1; reason: Lean indexing convention; the same instances
--   - encoding: n agents → `[NeZero n]`, i.e. n ≥ 1; reason: with no agents and at least one task there is no allocation and no make-span; the paper's n agents are at least one
--   - reading: declarations d^i chosen "in an unrestricted manner" (Def. 18), while the agents' declarations "are simply to report their types" (Def. 19) and types lie in [a, b]^k (Def. 33) → every declaration (the agent's own and the others') ranges over [a, b]^k; reason: the rounding algorithm is defined only on bounded instances (Def. 33); on unbounded rounded instances exact scheduling on unrelated machines is NP-hard, so no polynomial exact solver exists there
--   - encoding: dominance against all strategies of the other agents (Def. 3) → dominance quantifies over all profiles of the others with in-box declarations and unconstrained executions; reason: agent i's utility depends on the others only through their declarations (Def. 22 uses declared times for their tasks; proof of Claim 5.2, p. 188), so constraining their executions changes nothing
--   - encoding: the bonus uses the allocation x(t̂) and the compensation x(t) (Def. 34) → one allocation `allocOf f δ d`, computed from the δ-unit instance `units δ d`; reason: the algorithm reads only the rounded instance, and ⌈roundUp δ v / δ⌉ = ⌈v / δ⌉, so x(t̂) = x(t)
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001) 166–196, doi:10.1006/game.1999.0790, proof (sketch) of Theorem 5.9, p. 193 (PDF p. 28), middle sentence: "Arguments similar to those in 5.1, therefore, show that the only dominant strategies for agent i are to declare on a type t′^i such that t′^i and t^i have the same rounded value, and to execute its tasks such that after rounding, corr^i(x(t), t, t̃) equals corr∗(x(t), t)."

import Mathlib
import Definitions.Def_NisanRonen_Rounding_IsDominant
import Definitions.Def_NisanRonen_Rounding_IsExactRoundedSolver

namespace NisanRonen.Rounding

/-- **Characterization of the dominant strategies of the rounding mechanism** (Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001),
proof (sketch) of Theorem 5.9, p. 193, middle sentence, in corrected form: "Arguments similar to
those in 5.1, therefore, show that the only dominant strategies for agent i are to declare on a
type t′^i such that t′^i and t^i have the same rounded value, and to execute its tasks such that
after rounding, corr^i(x(t), t, t̃) equals corr∗(x(t), t)").

In the bounded problem with grid `δ > 0` and an exact rounded solver `f`, let `t` have entries in
`[a, b]` and let `σ` be an admissible strategy of agent `i` (declaration in `[a, b]^k`, every
allocated task executed in time `≥ t^i_j`). Then `σ` is dominant if and only if, for every
profile `s` of the other agents with declarations in `[a, b]^k`, writing `d` for the declarations
when `i` plays `σ` and `x = x(d)`, the rounded make-span of agent `i`'s corrected time vector is
optimal for the rounded instance in which `i`'s declaration is replaced by its true type:
`ĝ(x, corr^i(x, d, e^i(x))) ≤ ĝ(y, corr*(y, (d^{−i}, t^i)))` for every allocation `y`.

**Formalization Note** The printed sentence claims more: that every dominant declaration has the
same rounded value as the type. That claim is false (an agent of type `(3δ, 3δ)` on the grid
`{3δ, 4δ, 5δ}` has the dominant declaration `(4δ, 3δ)` under lexicographic tie-breaking), so only
this equivalence, which is what the arguments of Section 5.1 give, is stated. -/
theorem dominant_iff_rounded_optimal {n k : ℕ} [NeZero n] {a b δ : ℝ} (ha : 0 < a) (hab : a < b)
    (hδ : 0 < δ) (f : List (Fin n → ℕ) → List (Fin n)) (hf : IsExactRoundedSolver f δ a b)
    (t : Fin n → Fin k → ℝ) (ht : ∀ i j, a ≤ t i j ∧ t i j ≤ b) (i : Fin n) (σ : Strategy n k)
    (hσ : IsValid a b (t i) i σ) :
    IsDominant f δ a b i (t i) σ ↔
      ∀ s : Fin n → Strategy n k,
        (∀ l, l ≠ i → ∀ j, a ≤ (s l).decl j ∧ (s l).decl j ≤ b) →
        let d : Fin n → Fin k → ℝ := fun l => (Function.update s i σ l).decl
        let x := allocOf f δ d
        ∀ y : Fin k → Fin n,
          roundedMakespan δ x (corr i x d (σ.exec x)) ≤
            roundedMakespan δ y (corrStar y (Function.update d i (t i))) := by sorry

end NisanRonen.Rounding
