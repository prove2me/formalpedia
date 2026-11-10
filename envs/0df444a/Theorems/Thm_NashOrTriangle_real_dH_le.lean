-- Prove2me | Theorems.Thm_NashOrTriangle_real_dH_le
-- name    : NashOrTriangle.real_dH_le
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:47:08.883754+00:00
-- url     : https://prove2.me/theorems/572aec63-ff44-42e0-ab94-7cfee419a776
-- title:
--   Appendix C.2 — no $(t,\gamma)$-triangle ⇒ $d_H(u)\le t$ for $u\ge\gamma$
-- statement:
--   Let $H$ be a finite game with payoffs in $[0,1] \cap \mathbb Q$ and no $(t, \gamma)$-triangle. Then for every $u > 0$ with $u \ge \gamma$,
--   $$
--   d_H(u) \le t ,
--   $$
--   by the same deletion and reversal argument as for binary games. In the proof of Theorem 2.1(b) it is applied at $u = ah \ge \gamma$.
--
--   Differences from the source:
--   - encoding: d_H(u) ≤ t for u ≥ γ → TriangleDimLE M u t for u > 0 and γ ≤ u; reason: u > 0 is the domain of d_H ("For a finite game H and u > 0"); the predicate form of the bound
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962…66f7), Appendix C.2, p.26 (PDF p.27)

import Mathlib
import Definitions.Def_NashOrTriangle_IsPayoff
import Definitions.Def_NashOrTriangle_HasMarginTriangle
import Definitions.Def_NashOrTriangle_TriangleDimLE

namespace NashOrTriangle

/-- **Appendix C.2, real-valued games: `d_H(u) ≤ t` for `u ≥ γ`.** If the finite game `H` has no
`(t, γ)`-triangle, then `d_H(u) ≤ t` for every `u > 0` with `u ≥ γ`.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), Appendix C.2, printed p. 26 (PDF p. 27): "Also dH(u) ≤ t for u ≥ γ, by the same deletion
and reversal argument used for binary games."

**Formalization Note** `u > 0` is the domain of `d_H` ("For a finite game H and u > 0"). -/
theorem real_dH_le {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (M : A → B → ℚ) (hP : IsPayoff M) (t : ℕ) (γ : ℝ) (hT : ¬ HasMarginTriangle M t γ)
    (u : ℝ) (hu : 0 < u) (hγu : γ ≤ u) : TriangleDimLE M u t := by sorry

end NashOrTriangle
