-- Prove2me | Theorems.Thm_OnlineSetCover_Weighted_lemma_3_3
-- name    : OnlineSetCover.Weighted.lemma_3_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:05:55.803982+00:00
-- url     : https://prove2.me/theorems/6a1be584-f6a7-46bf-9eeb-8bbb1f6ae2d3
-- title:
--   Lemma 3.3 — an augmentation step never increases the potential, so the algorithm never fails
-- statement:
--   Let $\alpha > 0$ and consider the potential
--
--   $$\Phi(w,\mathcal C) = \sum_{j \notin C} n^{2 w_j} + n \cdot \exp\Big(\frac{1}{2\alpha} \sum_{S \in \mathcal S} \big(c_S \chi_{\mathcal C}(S) - 3 w_S c_S \log n\big)\Big)$$
--
--   of the weighted online set-cover algorithm (Section 3), where $n = |X|$, $w_j = \sum_{S \ni j} w_S$, and $C$ is the set of elements covered by $\mathcal C$.
--
--   1. For any weights $w$, any cover $\mathcal C$ and any set $S$ with $w_S \ge 0$ and $c_S \le \alpha$, the per-set substep of a weight augmentation for $S$ (multiply $w_S$ by $1 + \frac{1}{n c_S}$; if $S \notin \mathcal C$, add $S$ when this does not increase $\Phi$; FAIL if $\Phi$ has increased) does not fail, and the resulting weights $w'$ and cover $\mathcal C'$ satisfy
--   $$\Phi(w', \mathcal C') \le \Phi(w, \mathcal C).$$
--   2. In particular, if every set costs at most $\alpha$, then on every arrival sequence the algorithm never reaches FAIL.
--
--   The hypothesis $c_S \le \alpha$ is the paper's footnote 1 (p. 367): the algorithm has discarded every set costing more than $\alpha \ge c(\mathcal C_{OPT})$. The proof needs it in step (5): the inequality $e^y - 1 \le 3y/2$ holds only for $0 \le y \le 1/2$, with $y = c_S/(2\alpha)$.
--
--   This lemma is what keeps $\Phi$ below $n^2$ for the whole run, the invariant behind both parts of Theorem 3.4.
--
--   **Formalization Note** Part 1 is stated for arbitrary weights with $w_S \ge 0$ rather than only for weights the algorithm reaches; the algorithm's weights are always positive. Part 2 assumes only $c_S \le \alpha$ for every set, which is how the proof uses $\alpha \ge c(\mathcal C_{OPT})$.
-- source:
--   Alon, Awerbuch, Azar, Buchbinder, Naor, The Online Set Cover Problem, SIAM J. Comput. 39(2) (2009), p. 366, Lemma 3.3 (proof pp. 366–367, eqs. (1)–(6), footnote 1)

import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_potential
import Definitions.Def_OnlineSetCover_Weighted_Run

open OnlinePrimalDual.OnlineSetCover

namespace OnlineSetCover.Weighted

/-- **Lemma 3.3** (Alon, Awerbuch, Azar, Buchbinder, Naor 2009, p. 366). (1) For any weights `w`
with `w S ≥ 0`, any cover `C`, and any set `S` with `c_S ≤ α` (footnote 1, p. 367), the per-set
substep (a)–(c) for `S` does not fail, and the potential after it is at most the potential
before. (2) In particular, if every set costs at most `α`, the algorithm never reaches `FAIL`. -/
theorem lemma_3_3 {X T : Type*} [Fintype X] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance X T) (α : ℝ) (hα : 0 < α) :
    (∀ (w : T → ℝ) (C : Finset T) (S : T), 0 ≤ w S → inst.c S ≤ α →
        ∃ (w' : T → ℝ) (C' : Finset T), processSet inst α w C S = some (w', C') ∧
          potential inst w' C' α ≤ potential inst w C α) ∧
      ((∀ S, inst.c S ≤ α) → ∀ σ : List X, ¬ Reachable inst α σ (.fail : Config X T)) := by sorry

end OnlineSetCover.Weighted
