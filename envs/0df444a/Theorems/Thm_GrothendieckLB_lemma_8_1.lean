-- Prove2me | Theorems.Thm_GrothendieckLB_lemma_8_1
-- name    : GrothendieckLB.lemma_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:50:07.150198+00:00
-- url     : https://prove2.me/theorems/d6a742db-db55-4ba8-a8dd-b91e6f39a735
-- title:
--   Lemma 8.1: one-dimensional rearrangement
-- statement:
--   Let $S\sim N(0,1)$ and $x\in[0,1]$. Then
--   $$
--   \sup_{\substack{|A|\le1\\ \mathbb E[A(S)S]=\nu x}}\mathbb E\big[A(S)(S^3-3S)\big]=-\nu\Delta(x),
--   $$
--   the supremum running over measurable $A:\mathbb R\to[-1,1]$. This answers how small the cubic coefficient of a bounded function can be, given its linear coefficient, and it yields the diagonal bound.
--
--   Differences from the source:
--   - encoding: A : ℝ → [−1, 1] → A measurable with |A| ≤ 1; reason: the expectations E[A(S)S], E[A(S)(S³ − 3S)] are defined only for measurable A, and the page's maximizer A* = sgn(S)sgn(S² − r²) is measurable, so the supremum is unchanged
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Lemma 8.1, p.34

import Mathlib
import Definitions.Def_GrothendieckLB_stdExp
import Definitions.Def_ABPOnline_cG
import Definitions.Def_GrothendieckLB_Delta

namespace GrothendieckLB

/-- Lemma 8.1, one-dimensional rearrangement (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Lemma 8.1, p.34): for `S ∼ N(0, 1)` and
`x ∈ [0, 1]`, the supremum of `E[A(S)(S³ − 3S)]` over measurable `A : ℝ → [−1, 1]` with
`E[A(S)S] = νx` equals `−νΔ(x)`.

`ABPOnline.cG` is the published constant `ν = √(2/π) = E|Z|` (p.31). -/
theorem lemma_8_1 (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    IsLUB {y : ℝ | ∃ A : ℝ → ℝ, Measurable A ∧ (∀ s, |A s| ≤ 1) ∧
        stdExp (fun s => A s * s) = ABPOnline.cG * x ∧
        y = stdExp (fun s => A s * (s ^ 3 - 3 * s))}
      (-(ABPOnline.cG * Delta x)) := by sorry

end GrothendieckLB
