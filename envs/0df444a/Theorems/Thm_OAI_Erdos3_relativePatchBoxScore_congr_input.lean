-- Prove2me | Theorems.Thm_OAI_Erdos3_relativePatchBoxScore_congr_input
-- name    : OAI.Erdos3.relativePatchBoxScore_congr_input
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T23:32:02.5982+00:00
-- url     : https://prove2.me/theorems/24039b31-da4d-4b51-a160-77d1159b4357
-- title:
--   The relative patch box score depends only on the input inside the box
-- statement:
--   Let $X$ be a finite type with decidable equality, $s, d \in \mathbb{N}$, $N : X \to \mathbb{N}$, and $f, g : \mathbb{Z}^X \to \mathbb{R}$ with $f(x) = g(x)$ for every $x$ in `integerBox N` (the box $\prod_i \{0, \dots, N_i - 1\} \subseteq \mathbb{Z}^X$). Let $\mathrm{target} \in \mathbb{R}$ and let $A$ be a `PolynomialPatch X s d` (OpenAI's structure bundling weights, a polynomial form and a kernel, with a real-valued evaluation $A.\mathrm{value}$ on $\mathbb{R}^X$). Then `relativePatchBoxScore N f target A` $=$ `relativePatchBoxScore N g target A`, where `relativePatchBoxScore N f a A` is the average over $x \in$ `integerBox N` of $(f(x) - a)\, A.\mathrm{value}(x)$.
--
--   Lean: `OAI.Erdos3.relativePatchBoxScore_congr_input` in `lean/OAI/Combinatorics/Progressions/Geometry/RelativePatchBoxRestriction.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B100` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/RelativePatchBoxRestriction.lean#L50

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B100

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem relativePatchBoxScore_congr_input {X : Type*} [Fintype X] [DecidableEq X]
    {s d : ℕ} (N : X → ℕ) {f g : (X → ℤ) → ℝ}
    (hfg : ∀ x ∈ integerBox N, f x = g x) (target : ℝ) (A : PolynomialPatch X s d) :
    relativePatchBoxScore N f target A = relativePatchBoxScore N g target A := by
  sorry

end Erdos3
end
end OAI
