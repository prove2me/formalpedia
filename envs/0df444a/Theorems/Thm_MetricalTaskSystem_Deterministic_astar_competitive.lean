-- Prove2me | Theorems.Thm_MetricalTaskSystem_Deterministic_astar_competitive
-- name    : MetricalTaskSystem.Deterministic.astar_competitive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:15:29.204981+00:00
-- url     : https://prove2.me/theorems/f6554467-99b4-4db1-8d88-cb974eb0b717
-- title:
--   Theorem 6.1 (= Theorem 1.2) — $A^*_d$ has competitive ratio at most $(2n-1)\psi(d)$
-- statement:
--   Let $(S,d)$ be a task system with $n\ge2$ states (the triangle inequality holds, $d$ need not be symmetric), and let $\psi(d)$ be its cycle offset ratio. The on-line continuous-time algorithm $A^*_d$ has competitive ratio at most $(2n-1)\psi(d)$: for every
--   $$w>(2n-1)\,\psi(d)$$
--   there is a constant $K$ such that
--   $$c_{A^*_d}(\mathbf T)\le w\,c_0(\mathbf T)+K$$
--   for every finite sequence $\mathbf T$ of nonnegative tasks and every initial state $s_0$, where $c_{A^*_d}$ is the continuous-time cost of $A^*_d$ and $c_0$ the discrete off-line optimum.
--
--   For metrical task systems $\psi(d)=1$, so combined with Lemma 3.1 this gives the upper bound $w(S,d)\le 2n-1$ of Theorem 1.1.
--
--   **Formalization Note** The algorithm is taken with any tie-breaking rule, supplied as a state sequence for each initial state. Its cost lies in $[0,\infty]$, so the bound also asserts that only finitely many transitions occur before time $m+1$; the right-hand side is truncated at $0$, which is harmless since $K$ may be taken nonnegative. "Competitive ratio at most $c$" is rendered as "$w$-competitive for every $w>c$". The requirement $n\ge2$ keeps $\psi(d)$ and $A^*_d$ defined.
-- source:
--   Borodin, Linial, Saks, An Optimal On-Line Algorithm for Metrical Task System, J. ACM 39(4) (1992), p. 755, Theorem 6.1 (= Theorem 1.2, p. 747)

import Mathlib
import Definitions.Def_MetricalTaskSystem_Deterministic_Model
import Definitions.Def_MetricalTaskSystem_Deterministic_ContinuousTime
import Definitions.Def_MetricalTaskSystem_Deterministic_AstarD

namespace MetricalTaskSystem.Deterministic

/-- **Theorem 6.1 = Theorem 1.2** (Borodin–Linial–Saks 1992, pp. 755 and 747). For any task
system `(S, d)` with `n ≥ 2` states (not necessarily symmetric), the continuous-time on-line
algorithm `A*_d` (with any tie-breaking, given for each initial state `s₀` by a state sequence
`seq s₀` satisfying `IsAstarSeq`) has competitive ratio at most `(2n − 1) ψ(d)`: for every
`w > (2n − 1) ψ(d)` there is a constant `K` with `c_{A*_d}(T) ≤ w · c₀(T) + K` for every
finite nonnegative task sequence `T` and every initial state `s₀`. -/
theorem astar_competitive {S : Type} [Fintype S] [DecidableEq S] [Nontrivial S]
    (d : S → S → ℝ) (hd : IsTaskSystem d)
    (seq : S → ℕ → S) (hseq : ∀ s₀, IsAstarSeq d s₀ (seq s₀))
    (w : ℝ) (hw : (2 * (Fintype.card S : ℝ) - 1) * cycleOffsetRatio d < w) :
    ∃ K : ℝ, ∀ (s₀ : S) (m : ℕ) (T : Fin m → S → ℝ), (∀ i s, 0 ≤ T i s) →
      astarCost d (seq s₀) T ≤ ENNReal.ofReal (w * offlineOpt d s₀ T + K) := by sorry

end MetricalTaskSystem.Deterministic
