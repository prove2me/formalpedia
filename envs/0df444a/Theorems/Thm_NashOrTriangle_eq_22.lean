-- Prove2me | Theorems.Thm_NashOrTriangle_eq_22
-- name    : NashOrTriangle.eq_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:45:26.972202+00:00
-- url     : https://prove2.me/theorems/51898068-cf9c-4fad-90d0-9baf72b8fd41
-- title:
--   Eq. (22) — binary game without $t$-triangle has $s_H(u)=O(t/u^2)$
-- statement:
--   There is a universal constant $C$ such that for every finite binary game $H$ with no $t$-triangle and every $u \in (0, 1]$,
--   $$
--   s_H(u) \le C\, \frac{t}{u^2} ,
--   $$
--   that is, some valid multiset size $s$ satisfies $s \le C t / u^2$. This sharp form of VC uniform convergence has no logarithmic factor; with $u = ah = a/(4k)$ it gives $s_H(ah) = O(tk^2)$ in the proof of Theorem 2.1(a).
--
--   Differences from the source:
--   - reading: s_H(u) = O(t/u²) (no range of u stated) → for u ∈ (0, 1]; reason: s_H(u) ≥ 1 always while Ct/u² < 1 for large u (e.g. a 1×1 game), so (22) is false for large u; it is used at u = ah ≤ 1/8
--   - encoding: s_H(u) = O(t/u²) → ∃ universal C, ∃ s with IsMultisetSize M u s and s ≤ C t / u²; reason: big-O with a constant uniform in t, H and u; s_H as a predicate
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962…66f7), Appendix C, p.24 (PDF p.25), display (22)

import Mathlib
import Definitions.Def_NashOrTriangle_IsPayoff
import Definitions.Def_NashOrTriangle_IsBinary
import Definitions.Def_NashOrTriangle_HasTriangle
import Definitions.Def_NashOrTriangle_IsMultisetSize

namespace NashOrTriangle

/-- **Eq. (22).** For a finite binary game `H` with no `t`-triangle, `s_H(u) = O(t/u²)`: there is a
universal `C` such that some valid multiset size `s` has `s ≤ C t / u²`, for every `u ∈ (0, 1]`.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), Appendix C, printed p. 24 (PDF p. 25), display (22).

**Formalization Note** `u ∈ (0, 1]`: `s_H(u) ≥ 1` always while `C t/u² < 1` for large `u`, so (22)
is read on the range where it is used (`u = ah ≤ 1/8`). -/
theorem eq_22 :
    ∃ C : ℝ, ∀ (t : ℕ) {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
      (M : A → B → ℚ), IsPayoff M → IsBinary M → ¬ HasTriangle M t →
      ∀ u : ℝ, 0 < u → u ≤ 1 →
        ∃ s : ℕ, IsMultisetSize M u s ∧ (s : ℝ) ≤ C * (t : ℝ) / u ^ 2 := by sorry

end NashOrTriangle
