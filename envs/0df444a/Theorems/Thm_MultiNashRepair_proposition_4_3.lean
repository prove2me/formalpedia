-- Prove2me | Theorems.Thm_MultiNashRepair_proposition_4_3
-- name    : MultiNashRepair.proposition_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:35:23.679349+00:00
-- url     : https://prove2.me/theorems/99241f96-279b-45b2-b37f-ec3f45715820
-- title:
--   Proposition 4.3 — a failed LP yields a legal repair with $\varsigma^+\ge c\varsigma+D-E$, $0\le E\le120u/m$
-- statement:
--   Fix admissible controls for $\sigma$, $m\ge m_0$, and a state reached by Algorithm 1 that is nonterminal and whose descent LP fails. Then the dual certificates and the historical information yield a feasible repair: on a game with rational payoffs a repair step exists, and every repair (every optimal dual, every choice of pure best responses) is legal. Let $E$ be the total correction deficit (3.9) and $D=\beta(G_0+QH)$ (3.6). Then
--   $$\varsigma^+\ge c\varsigma+D-E,\qquad0\le E\le\frac{120u}{m},\qquad h^+=c(h+t\gamma),\qquad H^+=c(H+t)\qquad(4.3),$$
--   and the update preserves $H^+\le L_0$ and $mh^+_i-H^+\le R_0H^+$ for each player $i$.
--
--   Differences from the source:
--   - reading: a failed LP yields a feasible repair → on rational-payoff games a repair step exists, and every repair is legal (`RepairLegal`: positive normalizer, probability vector with $t\gamma_i<1$, nonnegative budgets of total $1-\rho$ with prefixes $\ge\rho>0$, correction probabilities in $[0,1)$, mixed profiles); reason: the paper's games have rational payoffs, so the LP data and an optimal rational dual are rational; feasibility of the mixtures is what the proof checks
--   - generalization: the algorithm's optimal dual and best responses → every optimal dual and every pure best responses; reason: contains the algorithm's choices
--   - generalization: payoffs in $[0,1]\cap\mathbb Q$ → real payoffs in $[0,1]$ (`BoundedGame`), with rationality assumed only for the existence clause; reason: the run relation needs rational choices, so the remaining clauses hold verbatim on rational games
-- source:
--   J. Tang, S. Ding, C. Fang, Breaking the One-Player Extension Barrier: History-Aware Repair for Multiplayer Approximate Nash Equilibria, arXiv:2611.06076 (preprint; held version, sha256 34b911ed…5c14), Proposition 4.3, (4.3), p.11; proof p.32

import Mathlib
import Definitions.Def_NashAmplification_Filtering_Model
import Definitions.Def_MultiNashRepair_IDRH

open NashAmplification.Filtering (Mixed Utility Tuple BoundedGame)
open Finset

namespace MultiNashRepair

/-- **Proposition 4.3 (Finite-Step Guarantee for Dual-History Reweighted Repair)** (Tang, Ding,
Fang, arXiv:2611.06076, Proposition 4.3, (4.3), p.11).

At a nonterminal reachable iteration of Algorithm 1 with `m ≥ m0` whose descent LP fails, the
dual certificates and the historical information yield a feasible repair: on a game with rational
payoffs a repair step exists, and every repair (every optimal dual, every choice of pure best
responses) is legal — `G0 − Qτ > 0`, `γ` is a probability vector with `0 ≤ tγ_i < 1`, the reverse
budgets are nonnegative with total `1 − ρ` and prefixes at least `ρ > 0`, the correction
probabilities lie in `[0,1)`, and all profiles are mixed profiles. With `E` the total correction
deficit (3.9) and `D = β(G0 + QH)` (3.6): `ς⁺ ≥ cς + D − E`, `0 ≤ E ≤ 120u/m`,
`h⁺ = c(h + tγ)`, `H⁺ = c(H + t)` (4.3), and the update preserves `H⁺ ≤ L0` and
`m h⁺_i − H⁺ ≤ R0 H⁺` for each player `i`.

**Formalization Note.** "Feasible repair" is read as existence (rational payoffs give rational
LP data, hence a rational optimal dual) together with the legality clauses. -/
theorem proposition_4_3 {σ : ℚ} (ctrl : Controls σ) {m : ℕ} {n : Fin m → ℕ}
    (hm : ctrl.m0 ≤ m) (hn : ∀ i, 0 < n i) (u : Utility n) (hu : BoundedGame u)
    {kk : ℕ} {s : State n} (hs : Reach ctrl u kk s) (hterm : ¬ Terminal σ u s)
    (hfail : ¬ Passes ctrl u s) :
    ((∀ i a, IsRat (u i a)) → ∃ s' : State n, RepairStep ctrl u s s') ∧
    ∀ (w : (i : Fin m) → Fin (n i) → ℝ) (α : ℝ) (arev acor : (i : Fin m) → Fin (n i)),
      DualOptimal u s.x ctrl.η w α →
      IsRevBR u (rY ctrl.knobs s w) (rDelta ctrl.knobs s w) arev →
      IsFwdBR u (rXt ctrl.knobs s w arev) (rE ctrl.knobs u s w arev) acor →
      let k := ctrl.knobs
      let E := rEtot k u s w arev
      let s' := repairState k u s w arev acor
      RepairLegal k u s w arev ∧ AGT.IsMixedProfile s'.x ∧
        k.c * scaled u s.x + k.Dsh s.H - E ≤ scaled u s'.x ∧
        0 ≤ E ∧ E ≤ 120 * (ctrl.u : ℝ) / m ∧
        s'.h = k.c • (s.h + k.t • rGamma k s w) ∧ s'.H = k.c * (s.H + k.t) ∧
        s'.H ≤ k.L0 ∧ ∀ i, (m : ℝ) * s'.h i - s'.H ≤ k.R0 * s'.H := by sorry

end MultiNashRepair
