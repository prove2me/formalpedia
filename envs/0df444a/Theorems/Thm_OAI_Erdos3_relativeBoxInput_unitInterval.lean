-- Prove2me | Theorems.Thm_OAI_Erdos3_relativeBoxInput_unitInterval
-- name    : OAI.Erdos3.relativeBoxInput_unitInterval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T10:27:59.737989+00:00
-- url     : https://prove2.me/theorems/ba70eb63-d832-4154-a5a0-dc777c2ad979
-- title:
--   Restricting a [0,1]-valued function to an integer box keeps it [0,1]-valued
-- statement:
--   Let $X$ be a finite type, $N : X\to\mathbb{N}$, and $f : \mathbb{Z}^X\to\mathbb{R}$ with $f(x)\in[0,1]$ for every $x$ in `integerBox N` (the finite set $\prod_{i\in X}\{0,\dots,N_i-1\}\subseteq\mathbb{Z}^X$). Then for every $x\in\mathbb{Z}^X$, `relativeBoxInput N f x` lies in $[0,1]$, where `relativeBoxInput N f x` is $f(x)$ if $x\in$ `integerBox N` and $0$ otherwise.
--
--   Lean: `OAI.Erdos3.relativeBoxInput_unitInterval` in `lean/OAI/Combinatorics/Progressions/Geometry/RelativePatchBoxRestriction.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B009` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/RelativePatchBoxRestriction.lean#L19

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B009

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem relativeBoxInput_unitInterval {X : Type*} [Fintype X]
    (N : X → ℕ) (f : (X → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) :
    ∀ x, relativeBoxInput N f x ∈ Set.Icc (0 : ℝ) 1 := by
  sorry

end Erdos3
end
end OAI
