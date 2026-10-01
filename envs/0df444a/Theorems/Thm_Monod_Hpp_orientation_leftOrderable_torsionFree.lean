-- Prove2me | Theorems.Thm_Monod_Hpp_orientation_leftOrderable_torsionFree
-- name    : Monod.Hpp_orientation_leftOrderable_torsionFree
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-30T12:45:07.811442+00:00
-- url     : https://prove2.me/theorems/14e39eac-00b8-4b7e-94ad-1ba479d8802c
-- title:
--   p. 1 — H preserves the orientation of ℝ, is left-orderable, and is torsion-free
-- statement:
--   Every $h \in H$ maps $\mathbf{R} = \mathbf{P}^1 \setminus \{\infty\}$ to itself preserving order: if $x < y$ then $h(x) < h(y)$, both real. $H$ carries a left-invariant linear order ($a \le b \Rightarrow ca \le cb$). And $H$ is torsion-free: no non-identity element has a positive power equal to the identity.
-- source:
--   Monod, N., Groups of piecewise projective homeomorphisms, Proc. Natl. Acad. Sci. USA 110 (2013) 4524–4527, https://doi.org/10.1073/pnas.1218426110 (arXiv:1209.5229v2, whose page numbers are used), p. 1, the construction

import Mathlib
import Definitions.Def_Monod_PiecewiseProjective

namespace Monod

theorem Hpp_orientation_leftOrderable_torsionFree :
    (∀ h ∈ Hpp, ∀ x y : ℝ, x < y → ∃ x' y' : ℝ,
        h (x : OnePoint ℝ) = x' ∧ h (y : OnePoint ℝ) = y' ∧ x' < y') ∧
      (∃ r : LinearOrder Hpp, ∀ a b c : Hpp, r.le a b → r.le (c * a) (c * b)) ∧
      ∀ h : Hpp, h ≠ 1 → ∀ n : ℕ, 0 < n → h ^ n ≠ 1 := by
  sorry

end Monod
