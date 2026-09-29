-- Prove2me | Theorems.Thm_MetricalTaskSystem_Deterministic_astar_f_le_offline
-- name    : MetricalTaskSystem.Deterministic.astar_f_le_offline
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:14:56.688432+00:00
-- url     : https://prove2.me/theorems/16967dcc-dbd4-40c6-a0dc-c80862e643e4
-- title:
--   Lemma 6.2 — $h_k(s)\ge f_k(s)$: the off-line cost at the transition times dominates $f_k$
-- statement:
--   Let $(S,d)$ be a task system with at least two states, $s_0\in S$, and $T^1\cdots T^m$ a sequence of nonnegative tasks. Let $t_k$ be the time at which the algorithm $A^*_d$ enters its $k$-th state $s_k$ ($t_0=1$), and let
--   $$h_k(s)=\varphi_{t_k}(s)$$
--   be the minimum cost of an off-line continuous-time schedule up to time $t_k$ subject to being in state $s$ at time $t_k$. Then
--   $$h_k(s)\ge f_k(s)\qquad\text{for all }s\in S,$$
--   for every $k$ such that the transition time $t_k$ occurs.
--
--   The functions $f_k$ are thus lower bounds on the off-line cost, which is the first step in comparing $A^*_d$ with the optimum.
-- source:
--   Borodin, Linial, Saks, An Optimal On-Line Algorithm for Metrical Task System, J. ACM 39(4) (1992), p. 756, Lemma 6.2 (h_k defined on p. 755, φ_t on p. 754)

import Mathlib
import Definitions.Def_MetricalTaskSystem_Deterministic_Model
import Definitions.Def_MetricalTaskSystem_Deterministic_ContinuousTime
import Definitions.Def_MetricalTaskSystem_Deterministic_AstarD

namespace MetricalTaskSystem.Deterministic

/-- **Lemma 6.2** (Borodin–Linial–Saks 1992, p. 756). Let `t_k` be the time at which `A*_d`
enters `s_k` on the (nonnegative) task sequence `T¹ ⋯ Tᵐ` (`t₀ = 1`), and let
`h_k(x) = φ_{t_k}(x)` be the optimal off-line (continuous-time) cost up to time `t_k` subject
to being in state `x` at time `t_k`. Then `h_k(x) ≥ f_k(x)` for all states `x`. -/
theorem astar_f_le_offline {S : Type} [Fintype S] [DecidableEq S] [Nontrivial S]
    (d : S → S → ℝ) (hd : IsTaskSystem d) (s₀ : S) (s : ℕ → S) (hs : IsAstarSeq d s₀ s)
    (m : ℕ) (T : Fin m → S → ℝ) (hT : ∀ i x, 0 ≤ T i x)
    (k : ℕ) (tk : ℝ) (htk : entryTime s (cSeq d s) T k = some tk) (x : S) :
    fSeq d s k x ≤ offlineCostTo d s₀ T tk x := by sorry

end MetricalTaskSystem.Deterministic
