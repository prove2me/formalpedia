-- Prove2me | Theorems.Thm_Monod_contDiff_and_exists_mulEquiv_HRat_F
-- name    : Monod.contDiff_and_exists_mulEquiv_HRat_F
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-30T14:12:39.626354+00:00
-- url     : https://prove2.me/theorems/8f62bd66-7085-4119-8b50-210511d293ea
-- title:
--   p. 2 (Thurston) — H(ℤ) with rational breakpoints consists of C¹ maps and is conjugate to F
-- statement:
--   Let $H_{\mathbf{Q}}(\mathbf{Z})$ be the group of homeomorphisms of $\mathbf{P}^1$ fixing $\infty$, piecewise in $\mathrm{PSL}_2(\mathbf{Z})$ with breakpoints in $\mathbf{Q} \cup \{\infty\}$ (`HRat`). (i) Each element restricts on $\mathbf{R}$ to a $C^1$ function. (ii) There are an increasing bijection $c$ from $(0,1)$ onto $\mathbf{R}$ and an isomorphism $\varphi \colon H_{\mathbf{Q}}(\mathbf{Z}) \to F$ with $h(c(t)) = c(\varphi(h)(t))$ for all $h$ and all $t \in (0,1)$: conjugation by $c$ carries $H_{\mathbf{Q}}(\mathbf{Z})$ onto Thompson's group $F$ (Cannon–Floyd–Parry's $F$ on $[0,1]$).
-- source:
--   Monod, N., Groups of piecewise projective homeomorphisms, Proc. Natl. Acad. Sci. USA 110 (2013) 4524–4527, https://doi.org/10.1073/pnas.1218426110 (arXiv:1209.5229v2, whose page numbers are used), p. 2, after Problem 12

import Mathlib
import Definitions.Def_CannonFloydParry
import Definitions.Def_Monod_PiecewiseProjective

namespace Monod

theorem contDiff_and_exists_mulEquiv_HRat_F :
    (∀ h ∈ HRat, ∃ u : ℝ → ℝ, ContDiff ℝ 1 u ∧ ∀ x : ℝ, h (x : OnePoint ℝ) = u x) ∧
      ∃ c : ℝ → ℝ, StrictMonoOn c (Set.Ioo 0 1) ∧ c '' Set.Ioo 0 1 = Set.univ ∧
        ∃ φ : HRat ≃* CannonFloydParry.F, ∀ (h : HRat), ∀ t ∈ Set.Ioo (0 : ℝ) 1,
          (h : OnePoint ℝ ≃ₜ OnePoint ℝ) (c t : OnePoint ℝ) =
            (c (CannonFloydParry.extend (φ h : CannonFloydParry.UI ≃o CannonFloydParry.UI) t) :
              OnePoint ℝ) := by
  sorry

end Monod
