-- Prove2me | Theorems.Thm_NashOrTriangle_lemma_C4
-- name    : NashOrTriangle.lemma_C4
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:45:23.752092+00:00
-- url     : https://prove2.me/theorems/f0adba4d-ade2-4eb3-8941-e04058f1d549
-- title:
--   Lemma C.4 — no $(t,\gamma)$-triangle ⇒ $\mathrm{fat}(H,r)\le(t-1)(\lceil 2/r\rceil+1)+1$ for $2\gamma\le r\le1$
-- statement:
--   Let $H$ be a game with payoffs in $[0,1] \cap \mathbb Q$ and no $(t, \gamma)$-triangle. Then for every $r$ with $0 < r$ and $2\gamma \le r \le 1$,
--   $$
--   \mathrm{fat}(H, r) \le (t - 1)\bigl(\lceil 2/r \rceil + 1\bigr) + 1 = O(t/r),
--   $$
--   where $\mathrm{fat}(H, r)$ is the larger fat-shattering dimension, with separation $r$, of the two payoff classes of $H$. Excluding triangles at a single margin thus bounds the fat-shattering dimension at the corresponding scale, which feeds the Bartlett–Long bound (23).
--
--   Differences from the source:
--   - encoding: 2γ ≤ r ≤ 1 → 0 < r, 2γ ≤ r, r ≤ 1; reason: 0 < r makes 2/r meaningful; it follows from 2γ ≤ r whenever γ > 0, as for every γ = c/k of the paper
--   - encoding: fat(H, r) ≤ (t − 1)(⌈2/r⌉ + 1) + 1 = O(t/r) → FatLE M r ((t − 1) * (⌈2/r⌉₊ + 1) + 1); reason: the explicit bound; O(t/r) follows from it for r ≤ 1; fat via BartlettNN.Margin.fat at scale r/2
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962…66f7), Appendix C.2, Lemma C.4, p.26 (PDF p.27)

import Mathlib
import Definitions.Def_NashOrTriangle_IsPayoff
import Definitions.Def_NashOrTriangle_HasMarginTriangle
import Definitions.Def_NashOrTriangle_FatLE

namespace NashOrTriangle

/-- **Lemma C.4.** If a `[0, 1]`-valued game `H` has no `(t, γ)`-triangle, then for
`2γ ≤ r ≤ 1`, `fat(H, r) ≤ (t − 1)(⌈2/r⌉ + 1) + 1`.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), Appendix C.2, Lemma C.4, printed p. 26 (PDF p. 27).

**Formalization Note** `0 < r` makes `2/r` meaningful (it follows from `2γ ≤ r` whenever
`γ > 0`, as for every `γ = c/k` of the paper). The explicit bound is the statement; the paper's
"`= O(t/r)`" is its consequence. -/
theorem lemma_C4 {A B : Type} [Countable A] [Countable B] [Nonempty A] [Nonempty B]
    (M : A → B → ℚ) (hP : IsPayoff M) (t : ℕ) (γ r : ℝ) (hT : ¬ HasMarginTriangle M t γ)
    (hr : 0 < r) (hγr : 2 * γ ≤ r) (hr1 : r ≤ 1) :
    FatLE M r ((t - 1) * (⌈2 / r⌉₊ + 1) + 1) := by sorry

end NashOrTriangle
