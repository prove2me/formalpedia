-- Prove2me | Theorems.Thm_OnlinePrimalDual_OnlineSetCover_potential_nonincreasing_v2
-- name    : OnlinePrimalDual.OnlineSetCover.potential_nonincreasing_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:41:56.996021+00:00
-- url     : https://prove2.me/theorems/6b6b18c7-4742-4f63-bf23-74a8b09ccb70
-- title:
--   Lemma 5.1 — for a set of cost at most the current guess $\alpha$, the expected potential never increases
-- statement:
--   Consider the deterministic online set-cover algorithm of Section 5.1 for the current guess $\alpha$ of $c(C_{\mathrm{OPT}})$, with $n = |X| \ge 1$ elements known in advance, set costs $c_s > 0$, and the potential $\Phi(w, C) = \sum_{e \notin \bar C} n^{2 w_e} + n \exp\Big(\tfrac{1}{2\alpha}\sum_s \big(c_s\chi_C(s) - 3 w_s c_s \ln n\big)\Big)$, where $w_e = \sum_{s \ni e} w_s$ and $\bar C$ is the set of elements covered by $C$. Consider a step in which the weight of a set $s$ with $c_s \le \alpha$ is augmented from $w_s$ to $w'_s \ge w_s$ (all other weights unchanged) and $s$ is added to the cover $C$ with probability $p = 1 - n^{-2\delta_s}$, $\delta_s = w'_s - w_s$. Then the expected potential after the step does not exceed the potential before it:
--   $$p\,\Phi(w', C\cup\{s\}) + (1-p)\,\Phi(w', C) \le \Phi(w, C).$$
--
--   **Formalization Note.** The retired version omitted the standing bound $c_s \le \alpha$, and for a set costlier than the guess the growth factor $e^{c_s/(2\alpha)}$ of the second term dominates the $n^{-2\delta_s}$ discount (disproved with $c_s = 8\alpha$). The new statement adds the hypothesis $c_s \le \alpha$ and is otherwise the retired one (single-set augmentation step, the book's probability $1 - n^{-2\delta_s}$, the platform's `potential`). Conventions made explicit: for guess $\alpha$ the algorithm only ever uses sets of cost at most $\alpha$ (sets costlier than the guess are discarded for that guess — the standing convention of the guess-and-double scheme of Section 5.1, used in the proof to bound $e^{c_s/(2\alpha)}$); $n \ge 1$ so that $\log n$ is defined; the step is stated for an arbitrary state $(w, C)$, not only states the algorithm reaches, since the inequality holds for all of them. Correction to the printed source: none.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 4(2-3), 2009, p. 136-137, Lemma 5.1 (Section 5.1)

import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_potential

namespace OnlinePrimalDual.OnlineSetCover

/-- **Lemma 5.1** (Buchbinder & Naor, FnT TCS 2009, p. 137) — the potential-function monotonicity
Theorem 5.2 rests on. A step of the algorithm for the current guess `α` augments the weight of
a set `s` from `w s` to `w' s` (`w'` agreeing with `w` off `s`) and adds `s` to the cover with
probability `p = 1 − n^{−2δs}`, `δs = w' s − w s` (p. 137); the expected potential after the
step — the `p`-weighted average of the potential with `s` inserted into `C` and with `C`
unchanged — never exceeds the potential before the step. `hcs : c s ≤ α` is the standing
assumption of the algorithm for guess `α` (p. 136-137: only sets of cost at most the current
guess `α` of `c(COPT)` are ever used, costlier sets being discarded for that guess); the proof
bounds the growth factor `exp(cs/(2α))` of the second term using exactly this, and the retired
version, which omitted it, is false for `cs > α` (the exponential jump of the second term then
dominates the `n^{−2δs}` discount). `hE` (`n ≥ 1`) is the book's standing `n = |X|` with
`log n` defined. -/
theorem potential_nonincreasing_v2 {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (α : ℝ) (hα_pos : 0 < α)
    (w w' : T → ℝ) (C : Finset T) (s : T) (hcs : inst.c s ≤ α)
    (hw'_off : ∀ t, t ≠ s → w' t = w t) (hw'_ge : w s ≤ w' s)
    (hE : 1 ≤ Fintype.card E) :
    let n : ℝ := (Fintype.card E : ℝ)
    let p : ℝ := 1 - n ^ (-2 * (w' s - w s))
    p * potential inst w' (insert s C) α + (1 - p) * potential inst w' C α ≤
      potential inst w C α := by sorry

end OnlinePrimalDual.OnlineSetCover
