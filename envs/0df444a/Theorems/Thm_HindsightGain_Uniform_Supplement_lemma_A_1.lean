-- Prove2me | Theorems.Thm_HindsightGain_Uniform_Supplement_lemma_A_1
-- name    : HindsightGain.Uniform.Supplement.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:03:13.794241+00:00
-- url     : https://prove2.me/theorems/ae02b0d7-2255-4ce2-bf32-6d934487aaf2
-- title:
--   Lemma A.1 — Separation of $\beta$ and $\mathrm{mc}$ under $D_0$ and $D_1$
-- statement:
--   Let $0<\varepsilon\le1/64$ and $\theta=32\varepsilon$, and let $D_0=G(n,\tfrac12)$ and $D_1$ be the planted-bipartition law of Appendix A. For $n\ge4\cdot10^4$, with probability at least $0.99$ a graph $G$ drawn from $D_0$ satisfies
--   $$\beta(G)\ge\tfrac18n^2-3n^{3/2}\quad\text{and}\quad\mathrm{mc}(G)\le\tfrac18n^2+n^{3/2},$$
--   and with probability at least $0.99$ a graph drawn from $D_1$ satisfies
--   $$\beta(G)\le\tfrac18n^2-4\varepsilon n^2+2n^{3/2}\quad\text{and}\quad\mathrm{mc}(G)\ge\tfrac18n^2+4\varepsilon n^2-2n^{3/2}.$$
--
--   The two laws thus have values of $\beta$ and of $\mathrm{mc}$ separated by about $4\varepsilon n^2$.
--
--   Differences from the source:
--   - encoding: the laws D_0, D_1 and D_b^F → point masses on the graphs on Fin n and on Boolean answer vectors (true for an edge, X_e = +1); reason: the same finite laws
--   - encoding: θ := 32ε ≤ 1/2 from the appendix setting → hypotheses 0 < ε ≤ 1/64 and the explicit factor 32ε in D_1; reason: these are the standing assumptions of Appendix A
--   - encoding: an n-vertex graph → a Mathlib simple graph on Fin n; reason: finite simple graphs up to relabeling
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, Lemma A.1, p.33

import Mathlib
import Definitions.Def_HindsightGain_Uniform_Supplement_planted

set_option autoImplicit false

namespace HindsightGain.Uniform.Supplement

/-- Lemma A.1, p.33, for the Appendix A laws with `ε ∈ (0, 1/64]` (so `θ = 32ε ≤ 1/2`): both
inequalities hold jointly with probability at least `0.99` under `D_0`, and both hold jointly with
probability at least `0.99` under `D_1`. -/
theorem lemma_A_1 (n : ℕ) (ε : ℝ) (hn : 4 * 10 ^ 4 ≤ n) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 64) :
    99 / 100 ≤ graphProb (lawD0 n) (fun G =>
        (n : ℝ) ^ 2 / 8 - 3 * (n : ℝ) ^ ((3 : ℝ) / 2) ≤ bipDist G ∧
        (maxCut G : ℝ) ≤ (n : ℝ) ^ 2 / 8 + (n : ℝ) ^ ((3 : ℝ) / 2)) ∧
    99 / 100 ≤ graphProb (lawD1 n ε) (fun G =>
        bipDist G ≤ (n : ℝ) ^ 2 / 8 - 4 * ε * (n : ℝ) ^ 2 + 2 * (n : ℝ) ^ ((3 : ℝ) / 2) ∧
        (n : ℝ) ^ 2 / 8 + 4 * ε * (n : ℝ) ^ 2 - 2 * (n : ℝ) ^ ((3 : ℝ) / 2) ≤ (maxCut G : ℝ)) := by sorry

end HindsightGain.Uniform.Supplement
