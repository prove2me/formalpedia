-- Prove2me | Theorems.Thm_OnlineCarpoolingLei_Oblivious_backward_step
-- name    : OnlineCarpoolingLei.Oblivious.backward_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:42:46.442568+00:00
-- url     : https://prove2.me/theorems/93c50e7d-26d2-4ec9-99dc-8d2b3626426e
-- title:
--   Lemma 4.1 — the backward step raises the slack by at least one
-- statement:
--   Fix edges $e_1,\dots,e_T$ on $[n]$ and an integer $D\ge300$, and let $A$, $\Lambda$, $S^0,S^+,S^-$ be as in Section 4.1. Let $(d_t)_{0\le t\le T}$ be a trajectory ($d_0=0$, $d_t=d_{t-1}+\varepsilon_te_t$ with $\varepsilon_t\in\{-1,+1\}$) with receiving gap at most $29$. If $1\le t\le T$, $S\subseteq[n]$ is nonempty, and $e_t$ crosses $S$, then one of the sets $S'\in\{S^0,S^+,S^-\}$ satisfies
--   $$\Lambda(t-1,S')\ge\Lambda(t,S)+1 .$$
--   If moreover $\Lambda(t,S)\ge0$, then this choice has $S'\ne\emptyset$.
--
--   The trajectory is arbitrary: it need not be produced by the algorithm of Section 3. The integrality of the trajectory is what turns two gains summing to at least one into a gain of at least one. The lemma is the step of the backward walk in Lemma 4.2.
--
--   Differences from the source:
--   - encoding: vertex set $[n]$, edges $e_1,\dots,e_T$ → `Fin n`, `E : ℕ → Edge n` with $e_t$ = `E (t - 1)` (only the first $T$ entries matter); reason: relabelling and index shift
--   - encoding: integer $D\ge300$ → `D : ℕ` with `300 ≤ D`; reason: same set of values
--   - encoding: a signed-edge trajectory (d_t) for 0 ≤ t ≤ T → traj E ε restricted to 0,…,T, with ε : ℕ → ℤ and IsSignSeq ε; reason: every finite valid trajectory extends by arbitrary ±1 signs; neither conclusion depends on signs after T
-- source:
--   Yuhao Lei, STOC 2027 submission #416 (October 2026), Lemma 4.1, p.7 (PDF p.7); Section 4 preamble, p.6

import Mathlib
import Definitions.Def_OnlineCarpoolingLei_Oblivious_Model
import Definitions.Def_OnlineCarpoolingLei_Oblivious_Threshold

namespace OnlineCarpoolingLei.Oblivious

/-- Lemma 4.1 (p.7). Fix edges `e₁, …, e_T` and an integer `D ≥ 300` (§4 preamble). Let `(d_t)`
be a trajectory with receiving gap at most `29`. If `1 ≤ t ≤ T`, `S ⊆ [n]` is nonempty and `e_t`
crosses `S`, then one of `S' ∈ {S⁰, S⁺, S⁻}` satisfies `Λ(t − 1, S') ≥ Λ(t, S) + 1`; if moreover
`Λ(t, S) ≥ 0`, this choice has `S' ≠ ∅`. (Here `e_t = E (t − 1)`.) -/
theorem backward_step {n : ℕ} (E : ℕ → Edge n) (T D : ℕ) (hD : 300 ≤ D) (ε : ℕ → ℤ)
    (hε : IsSignSeq ε) (hgap : GapAtMost E ε T 29) (t : ℕ) (ht : 1 ≤ t) (htT : t ≤ T)
    (S : Finset (Fin n)) (hS : S.Nonempty) (hcross : (E (t - 1)).Crosses S) :
    ∃ S' ∈ ({S, splus (E (t - 1)) S, sminus (E (t - 1)) S} : Finset (Finset (Fin n))),
      slack D (traj E ε) t S + 1 ≤ slack D (traj E ε) (t - 1) S' ∧
        (0 ≤ slack D (traj E ε) t S → S'.Nonempty) := by sorry

end OnlineCarpoolingLei.Oblivious
