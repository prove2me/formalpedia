-- Prove2me | Theorems.Thm_GibbsTransition_SizeCopies_interval_invariant
-- name    : GibbsTransition.SizeCopies.interval_invariant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T21:53:01.221746+00:00
-- url     : https://prove2.me/theorems/5f79d8ea-b651-4aec-b3b1-393f7b332a7b
-- title:
--   Lemma 3.4 — Interval invariant
-- statement:
--   Let $0<\varepsilon\le1/16$ be the rational accuracy input, let $\theta\in[1/4,3/4]$, and run the overlapping interval search with $K=\lceil\log(1/(4\varepsilon))/\log(8/5)\rceil$. Assume each executed comparison returns $Z_k=0$ when $\phi_k<\theta-\gamma_k$ and $Z_k=1$ when $\phi_k>\theta+\gamma_k$. No condition is imposed inside the comparison margin. Then
--
--   $$\theta\in I_k\quad(0\le k\le K),\qquad |\widehat\theta-\theta|\le\varepsilon.$$
--
--   Here $\widehat\theta$ is the midpoint of the actual final interval $I_K$. This statement specifies the deterministic guarantee needed of the comparison procedure, rather than assuming correctness of a statistical learner.
--
--   Differences from the source:
--   - encoding: dyadic interval endpoints and comparison bits → rational exact updates driven by a Boolean sequence; reason: the initial endpoints and updates remain dyadic, and no approximation of the control field is introduced
-- source:
--   Yuhao Cai, Zhenzhang Li, STOC 2027 submission #1168 (October 2026), Lemma 3.4 and §3.1 standing definitions, printed p. 6 (PDF p. 8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1168.pdf

import Mathlib
import Definitions.Def_GibbsTransition_SizeCopies_Interval

namespace GibbsTransition.SizeCopies

/-- Lemma 3.4, for the actual overlapping updates and stopping count.
Answers inside the margin are unrestricted. -/
theorem interval_invariant (epsilon : ℚ) (he0 : 0 < epsilon)
    (he1 : epsilon ≤ 1/16) (theta : ℝ)
    (ht : theta ∈ Set.Icc (1/4 : ℝ) (3/4)) (z : ℕ → Bool)
    (hz : ∀ k < searchRounds epsilon,
      (((searchField z k : ℚ) : ℝ) < theta - (searchMargin z k : ℝ) → z k = false) ∧
      (theta + (searchMargin z k : ℝ) < (searchField z k : ℝ) → z k = true)) :
    (∀ k ≤ searchRounds epsilon,
      theta ∈ Set.Icc ((searchInterval z k).1 : ℝ) ((searchInterval z k).2 : ℝ)) ∧
    |(searchOutput z (searchRounds epsilon) : ℝ) - theta| ≤ (epsilon : ℝ) := by sorry

end GibbsTransition.SizeCopies
