-- Prove2me | Theorems.Thm_Monod_eventually_eq_self_of_mem_second_derived
-- name    : Monod.eventually_eq_self_of_mem_second_derived
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-30T13:03:57.737048+00:00
-- url     : https://prove2.me/theorems/ca76e884-a11b-418b-98e8-ad5c3e320130
-- title:
--   Lemma 13 — the second derived subgroup of ⟨f, g⟩ acts trivially near a common fixed point
-- statement:
--   Let $f, g \in H$ fix a common point $p \in \mathbf{P}^1$ (possibly $\infty$). Then every element $w$ of the second derived subgroup $\langle f, g\rangle'' = [[K, K], [K, K]]$, $K = \langle f, g\rangle$, is the identity on some neighbourhood of $p$ (depending on $w$).
-- source:
--   Monod, N., Groups of piecewise projective homeomorphisms, Proc. Natl. Acad. Sci. USA 110 (2013) 4524–4527, https://doi.org/10.1073/pnas.1218426110 (arXiv:1209.5229v2, whose page numbers are used), p. 3, Lemma 13

import Mathlib
import Definitions.Def_Monod_PiecewiseProjective

namespace Monod

theorem eventually_eq_self_of_mem_second_derived {f g : OnePoint ℝ ≃ₜ OnePoint ℝ}
    (hf : f ∈ Hpp) (hg : g ∈ Hpp) {p : OnePoint ℝ} (hfp : f p = p) (hgp : g p = p)
    {w : OnePoint ℝ ≃ₜ OnePoint ℝ}
    (hw : w ∈ ⁅⁅Subgroup.closure {f, g}, Subgroup.closure {f, g}⁆,
            ⁅Subgroup.closure {f, g}, Subgroup.closure {f, g}⁆⁆) :
    ∀ᶠ x in nhds p, w x = x := by
  sorry

end Monod
