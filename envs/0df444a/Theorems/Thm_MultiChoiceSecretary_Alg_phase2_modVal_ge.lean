-- Prove2me | Theorems.Thm_MultiChoiceSecretary_Alg_phase2_modVal_ge
-- name    : MultiChoiceSecretary.Alg.phase2_modVal_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:37:34.57097+00:00
-- url     : https://prove2.me/theorems/d3e38ec5-1dcf-47b2-9471-50a34c444732
-- title:
--   Proof sketch of Theorem 2.1, PDF p. 2 — the subset of Z selected by the algorithm has expected modified value ≥ (1/2 − √(1/k))v
-- statement:
--   Let $S$ be a finite set of non-negative reals, $k \ge 2$, $T$ the $k$ largest elements of $S$ and $v$ their sum. Run the recursive $k$-choice secretary algorithm on a uniformly random order of $S$, and consider only the elements it selects after the $m$-th arrival (its second phase; these all belong to $Z$). Their expected modified value, over the random order and all binomial draws, satisfies
--
--   $$\mathbb E\big[\mathrm{modval}(\text{phase-2 selection})\big] \;\ge\; \Big(\frac12 - \sqrt{\frac1k}\Big)v.$$
--
--   Together with the induction hypothesis applied to the first phase, this is the second half of the induction step in the proof of Theorem 2.1.
--
--   **Formalization Note.** The second phase is the second component of the algorithm's stage distribution, which records phase 1 and phase 2 separately; the cap of $k$ items counts both phases. No hypothesis is added.
-- source:
--   Kleinberg, A multiple-choice secretary algorithm with applications to online auctions, SODA 2005, PDF p. 2 (top of right column), proof sketch of Theorem 2.1, "… we find that the algorithm selects a subset of Z whose expected modified value is at least (1/2 − √(1/k))v."

import Mathlib
import Definitions.Def_MultiChoiceSecretary_Alg_Setting

namespace MultiChoiceSecretary.Alg

theorem phase2_modVal_ge (S : Finset ℝ) (hS : ∀ x ∈ S, 0 ≤ x) (k : ℕ) (h2k : 2 ≤ k) :
    (1 / 2 - Real.sqrt (1 / k)) * topSum S k ≤ expectedPhase2ModVal S k := by sorry

end MultiChoiceSecretary.Alg
