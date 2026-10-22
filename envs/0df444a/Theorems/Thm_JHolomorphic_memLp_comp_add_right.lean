-- Prove2me | Theorems.Thm_JHolomorphic_memLp_comp_add_right
-- name    : JHolomorphic.memLp_comp_add_right
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T16:06:20.957487+00:00
-- url     : https://prove2.me/theorems/dee4ce1f-4504-493b-b7a3-99ae00f0a5a0
-- title:
--   Translation preserves $L^q$ membership and norm on restricted measures
-- statement:
--   Let $E$ be a normed group, $\mu$ a translation-invariant measure on $\mathbb{C}$, $S\subseteq\mathbb{C}$ measurable, $q\in[0,\infty]$, and $a\in\mathbb{C}$. If $g\in L^q(S,\mu)$, then $g(\cdot+a)\in L^q(S-a,\mu)$ and
--   $$\|g(\cdot+a)\|_{L^q(S-a,\mu)}=\|g\|_{L^q(S,\mu)},\qquad S-a=\{z: z+a\in S\}.$$
--
--   **Formalization Note** $L^q$ membership and norms are `MemLp` and `eLpNorm` for the restricted measures `μ.restrict ((· + a) ⁻¹' S)` and `μ.restrict S`; translation invariance is `μ.IsAddRightInvariant`.
-- source:
--   Standard (weak derivatives and Lebesgue spaces).

import Definitions.Def_JHolomorphic_Setting
import Mathlib.MeasureTheory.Group.Measure

namespace JHolomorphic

open MeasureTheory Metric

/-- For a translation-invariant measure `μ` on `ℂ` and a measurable set `S`, if `g ∈ L^q(S)` then
`g(· + a) ∈ L^q(S - a)`, with the same norm. -/
theorem memLp_comp_add_right {E : Type*} [NormedAddCommGroup E] {μ : Measure ℂ}
    [μ.IsAddRightInvariant] {q : ENNReal} {g : ℂ → E} {S : Set ℂ} (hS : MeasurableSet S) (a : ℂ)
    (hg : MemLp g q (μ.restrict S)) :
    MemLp (fun z => g (z + a)) q (μ.restrict ((· + a) ⁻¹' S)) ∧
      eLpNorm (fun z => g (z + a)) q (μ.restrict ((· + a) ⁻¹' S)) = eLpNorm g q (μ.restrict S) := by
  sorry

end JHolomorphic
