-- Prove2me | Theorems.Thm_HindsightGain_Uniform_Supplement_lemma_A_2
-- name    : HindsightGain.Uniform.Supplement.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:04:02.932535+00:00
-- url     : https://prove2.me/theorems/d486b4c1-101e-487f-8f1a-8fe8b5c75e68
-- title:
--   Lemma A.2 — $\chi^2$-divergence of the answer laws equals a sum over even subgraphs
-- statement:
--   Let $0<\varepsilon\le1/64$ and $\theta=32\varepsilon$. Fix a set $F$ of distinct pairs of $[n]$, viewed as a simple query graph, and let $D_b^F$ be the law of the answers $(X_e)_{e\in F}$ under $D_b$. Then
--   $$1+\chi^2\big(D_1^F\,\big\|\,D_0^F\big)=\sum_{J\subseteq F\ \text{even}}\theta^{2|J|},$$
--   where $J$ is even if every vertex has even degree in $([n],J)$; the empty set contributes $1$.
--
--   The identity reduces indistinguishability of $D_0$ and $D_1$ by a fixed query set to counting even subgraphs of the query graph.
--
--   Differences from the source:
--   - encoding: the laws D_0, D_1 and D_b^F → point masses on the graphs on Fin n and on Boolean answer vectors (true for an edge, X_e = +1); reason: the same finite laws
--   - encoding: θ := 32ε ≤ 1/2 from the appendix setting → hypotheses 0 < ε ≤ 1/64 and the explicit factor 32ε in D_1; reason: these are the standing assumptions of Appendix A
--   - encoding: a set F of distinct pairs → a finite set of non-diagonal elements of Sym2 (Fin n); reason: unordered pairs of distinct vertices
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, Lemma A.2, p.34

import Mathlib
import Definitions.Def_HindsightGain_Uniform_Supplement_planted

set_option autoImplicit false
open Classical
open scoped BigOperators

namespace HindsightGain.Uniform.Supplement

/-- Lemma A.2, p.34: for every fixed set `F` of distinct pairs (a simple query graph on `[n]`) and
`θ = 32ε`, `1 + χ²(D_1^F ‖ D_0^F) = Σ_{J ⊆ F even} θ^{2|J|}`; the empty set contributes `1`. -/
theorem lemma_A_2 (n : ℕ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 64)
    (F : Finset (Sym2 (Fin n))) (hF : ∀ z ∈ F, ¬ z.IsDiag) :
    1 + chiSq (answerLaw (lawD1 n ε) F) (answerLaw (lawD0 n) F) =
      ∑ J ∈ F.powerset, if IsEvenEdgeSet J then (32 * ε) ^ (2 * J.card) else 0 := by sorry

end HindsightGain.Uniform.Supplement
