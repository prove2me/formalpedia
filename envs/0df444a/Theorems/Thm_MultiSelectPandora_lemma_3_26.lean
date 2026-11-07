-- Prove2me | Theorems.Thm_MultiSelectPandora_lemma_3_26
-- name    : MultiSelectPandora.lemma_3_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:28:19.095731+00:00
-- url     : https://prove2.me/theorems/1c367fc0-7277-450d-bad4-63380e687d7c
-- title:
--   Lemma 3.26 — the mixed phase: rounding large entries does not change the floor
-- statement:
--   Let $I$ be a valid instance with $0<\mathrm{OPT}$, $k\ge1$ and $0<\varepsilon<1$. Run $I^S$ and $I^{SL}$ from $0$ along the same sequence of actions and realizations, with states $\alpha_t$ and $\alpha_t^{SL}$. For every step $t$ such that $\alpha_{t'}$ is not fully large for any $t'<t$:
--
--   1. $\alpha_t^{SL}$ is the entrywise $D^L$-rounding of $\alpha_t$;
--   2. $\alpha_t$ is fully large if and only if $\alpha_t^{SL}$ is, so the two become fully large at the same step $t^*$;
--   3. if $\alpha_t$ is not fully large, the two have the same floor, and the marginal rewards of the next step agree.
--
--   This is the observation that makes $k\ge2$ work: while the floor is small, the rounding of large entries is invisible.
--
--   Differences from the source:
--   - encoding: "Run IS and ISL with the same actions and realizations" → along every finite sequence of actions and positions, with the clauses stated for each step t before which no state is fully large; reason: this covers all steps up to and including t*
--   - reading: ε unrestricted → ε < 1; reason: b_i is small only for ε < 1, p.14
--   - encoding: no hypothesis on OPT → 0 < OPT; reason: θ = OPT^/ε is 0 when OPT = 0 and p.14 divides by it, so this excludes only an undefined case
--   - reading: the grid of Definition 3.21 written with ε OPT → the grid with ε OPT^; reason: footnote 1: "the algorithm uses ε OPT^", as OPT is not known; Φ changes by at most 2ε OPT within a cell
--   - reading: ⊤ is "an arbitrary fixed number greater than MaxV" (footnote 2) → ⊤ is a number above MaxV and above every value of the instance; reason: Remark A.4 and Claim A.7 need D^L(v) ≥ v for every v; with ⊤ = MaxV + 1 Claim 3.30 fails (two boxes, value 1000 with probability 0.1, else 0, c = 90, k = 1, ε = 1/4; gap 5.23)
--   - encoding: a law Fi with finite support → explicit support positions with values and probabilities, and expectations as finite sums with independence by product form; reason: p.5: "Each Fi is given explicitly, with finite support"
--   - encoding: "every constant k"; the searcher selects k prizes → k ≥ 1; reason: at k = 0 nothing can be selected, and the state has no floor
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Lemma 3.26, p.16 (PDF p.17); proof p.33 (PDF p.34)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_Inst_Valid
import Definitions.Def_MultiSelectPandora_OPT
import Definitions.Def_MultiSelectPandora_stFloor
import Definitions.Def_MultiSelectPandora_theta
import Definitions.Def_MultiSelectPandora_DL
import Definitions.Def_MultiSelectPandora_IS
import Definitions.Def_MultiSelectPandora_ISL
import Definitions.Def_MultiSelectPandora_DPData_runTrace
import Definitions.Def_MultiSelectPandora_DPAct

namespace MultiSelectPandora

/-- **Lemma 3.26 (mixed phase)**, p.16 (PDF p.17); proof p.33 (PDF p.34). Beyhaghi–Han–Luqman manuscript.

Run `I^S` and `I^SL` with the same actions and realizations. As long as `α_t` is not fully large, neither is `α^SL_t`, the two have the same floor, and the two marginal rewards agree. They become fully large at the same step `t*`, and `α^SL_{t*}` is the entrywise `D^L`-rounding of `α_{t*}`.

**Formalization Note.** Fix a trace and a step `t` such that the states before `t` are not fully large. Then `α^SL_t` is the entrywise `D^L`-rounding of `α_t` (the proof's induction, and at `t*` the last clause of the page). The two are fully large together. If they are not, the floors agree and so does the reward of step `t`. `ε < 1` is what makes `b_i` small (p.14). `0 < OPT` excludes `θ = 0`. -/
theorem lemma_3_26 (I : Inst) (hI : I.Valid) (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hOPT : 0 < OPT I k) (tr : List (DPAct I.n × ℕ)) (t : ℕ) (ht : t ≤ tr.length)
    (hbefore : ∀ t' < t, stFloor ((IS I k ε).runTrace (tr.take t') (0 : Fin k → ℝ)).1 < theta I k ε) :
    (∀ j, ((ISL I k ε).runTrace (tr.take t) (0 : Fin k → ℝ)).1 j =
      DL I k ε (((IS I k ε).runTrace (tr.take t) (0 : Fin k → ℝ)).1 j)) ∧
    (theta I k ε ≤ stFloor ((IS I k ε).runTrace (tr.take t) (0 : Fin k → ℝ)).1 ↔
      theta I k ε ≤ stFloor ((ISL I k ε).runTrace (tr.take t) (0 : Fin k → ℝ)).1) ∧
    (stFloor ((IS I k ε).runTrace (tr.take t) (0 : Fin k → ℝ)).1 < theta I k ε →
      stFloor ((ISL I k ε).runTrace (tr.take t) (0 : Fin k → ℝ)).1 =
        stFloor ((IS I k ε).runTrace (tr.take t) (0 : Fin k → ℝ)).1 ∧
      ((IS I k ε).runTrace ((tr.drop t).take 1)
          ((IS I k ε).runTrace (tr.take t) (0 : Fin k → ℝ)).1).2 =
        ((ISL I k ε).runTrace ((tr.drop t).take 1)
          ((ISL I k ε).runTrace (tr.take t) (0 : Fin k → ℝ)).1).2) := by sorry

end MultiSelectPandora
