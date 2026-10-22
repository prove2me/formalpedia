-- Prove2me | Theorems.Thm_JHolomorphic_HasWeakPartialsOn_smul_sub
-- name    : JHolomorphic.HasWeakPartialsOn.smul_sub
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T16:00:45.567974+00:00
-- url     : https://prove2.me/theorems/265b53fc-4b35-4f3b-8ea4-ebd4dab47ac6
-- title:
--   Weak partial derivatives of $c\,(f-g)$
-- statement:
--   Let $E$ be a real normed space and $U\subseteq\mathbb{C}$. Suppose $f_s,f_t$ are weak partial derivatives of $f:\mathbb{C}\to E$ on $U$ and $g_s,g_t$ are weak partial derivatives of $g$ on $U$, and that $f,f_s,f_t,g,g_s,g_t$ are integrable on every compact subset of $U$. Then for every $c\in\mathbb{R}$ the functions $c\,(f_s-g_s)$ and $c\,(f_t-g_t)$ are weak partial derivatives of $c\,(f-g)$ on $U$.
--   This is the linearity of weak differentiation, in the form used for difference quotients.
--
--   **Formalization Note** Weak partial derivatives are `HasWeakPartialsOn`, tested against real $C^\infty$ functions with compact support in the given open set; the first weak partial is the derivative in the direction $1$ and the second in the direction $i$.
-- source:
--   Standard (weak derivatives and Lebesgue spaces).

import Definitions.Def_JHolomorphic_Setting

namespace JHolomorphic

open MeasureTheory Metric
open scoped ContDiff

/-- Weak partial derivatives of `c • (f - g)`: if `f` and `g` have weak partials on `U` and all six
functions are integrable on compact subsets of `U`, then `c • (f - g)` has weak partials
`c • (fₛ - gₛ)` and `c • (fₜ - gₜ)` on `U`. -/
theorem HasWeakPartialsOn.smul_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set ℂ} {f fs ft g gs gt : ℂ → E} (hf : HasWeakPartialsOn U f fs ft)
    (hg : HasWeakPartialsOn U g gs gt)
    (hfi : ∀ K ⊆ U, IsCompact K → IntegrableOn f K ∧ IntegrableOn fs K ∧ IntegrableOn ft K)
    (hgi : ∀ K ⊆ U, IsCompact K → IntegrableOn g K ∧ IntegrableOn gs K ∧ IntegrableOn gt K)
    (c : ℝ) :
    HasWeakPartialsOn U (fun z => c • (f z - g z)) (fun z => c • (fs z - gs z))
      (fun z => c • (ft z - gt z)) := by
  sorry

end JHolomorphic
