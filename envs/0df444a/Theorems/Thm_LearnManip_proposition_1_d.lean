-- Prove2me | Theorems.Thm_LearnManip_proposition_1_d
-- name    : LearnManip.proposition_1_d
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:58:23.09946+00:00
-- url     : https://prove2.me/theorems/fdb21bf9-5d69-491b-a42d-3745638151b7
-- title:
--   Proposition 1(d), p.14 — $G$ is nonincreasing in $\eta$
-- statement:
--   Let $\eta_1\le\eta_2$ and let two parameter sets differ only in $\eta$. If $g_1,g_2$ are in the growth class and solve (15) for $\eta_1$ and $\eta_2$ respectively, then for all $s,c\ge0$,
--   $$g_2(s,c)\le g_1(s,c).$$
--
--   The proof of Theorem 1, p.34, uses this to reduce the case $\eta>1$ to $\eta=1$. There it prints "nondecreasing", but its argument needs the sign stated here, which is also that of the proposition.
--
--   Differences from the source:
--   - reading: G, the manipulation value, as a function of η → the solutions of (15) in the growth class, for two values of η; reason: Theorem 1 shows these exist and are unique
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), Proposition 1(d), p.14

import Mathlib
import Definitions.Def_LearnManip_Params
import Definitions.Def_LearnManip_IsManipValue
import Definitions.Def_LearnManip_GClass

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory InformationTheory Filter

namespace LearnManip

/-- Proposition 1(d), p.14, of Keppo, Kim, Zhang (SSRN 3465030, 2021-09-04): the manipulation value is
nonincreasing in `η` on `[0, ∞)`. (The proof of Theorem 1, p.34, prints "nondecreasing"; its argument
needs this sign.)

**Formalization Note.** Stated for the solutions of (15) in the growth class, which `theorem_1` shows
exist and are unique, for two parameter sets differing only in `η`. -/
theorem proposition_1_d (P₁ P₂ : Params) (hα : P₁.α = P₂.α) (hγ : P₁.γ = P₂.γ) (hη : P₁.η ≤ P₂.η)
    {g₁ g₂ : ℝ≥0 → ℝ≥0 → ℝ} (hg₁ : GClass g₁) (hg₂ : GClass g₂)
    (hm₁ : IsManipValue P₁ g₁) (hm₂ : IsManipValue P₂ g₂) (s c : ℝ≥0) :
    g₂ s c ≤ g₁ s c := by sorry

end LearnManip
