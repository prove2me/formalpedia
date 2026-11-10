-- Prove2me | Theorems.Thm_NashOrTriangle_binary_dH_le
-- name    : NashOrTriangle.binary_dH_le
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:46:36.150357+00:00
-- url     : https://prove2.me/theorems/1665342b-735b-419c-9fef-d8b089f1c3d0
-- title:
--   Appendix C — binary game without $t$-triangle has $d_H(u)\le t$ for all $u>0$
-- statement:
--   Let $H$ be a finite binary game with no $t$-triangle. Then for every $u > 0$,
--   $$
--   d_H(u) \le t ,
--   $$
--   that is, neither $H$ nor the complemented game $1 - H$ contains a triangle of size $t + 1$ with margin $u$. Together with (22) this bounds both parameters of Lemma C.1 on binary games.
--
--   Differences from the source:
--   - encoding: d_H(u) ≤ t → TriangleDimLE M u t: no (t+1, u)-triangle in M or in complement M; reason: the predicate form of the bound, without a junk-valued maximum
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962…66f7), Appendix C, p.24 (PDF p.25)

import Mathlib
import Definitions.Def_NashOrTriangle_IsPayoff
import Definitions.Def_NashOrTriangle_IsBinary
import Definitions.Def_NashOrTriangle_HasTriangle
import Definitions.Def_NashOrTriangle_TriangleDimLE

namespace NashOrTriangle

/-- **Appendix C, binary games: `d_H(u) ≤ t`.** If the finite game `H` is binary with no
`t`-triangle, then `d_H(u) ≤ t` for every `u > 0`.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), Appendix C, printed p. 24 (PDF p. 25): "If H is binary with no t-triangle, then
dH(u) ≤ t for every u > 0." -/
theorem binary_dH_le {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (M : A → B → ℚ) (hP : IsPayoff M) (hB : IsBinary M) (t : ℕ) (hT : ¬ HasTriangle M t)
    (u : ℝ) (hu : 0 < u) : TriangleDimLE M u t := by sorry

end NashOrTriangle
