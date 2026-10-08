-- Prove2me | Theorems.Thm_OAI_Erdos3_FiniteProbabilityWeights_complexMean_congr_support
-- name    : OAI.Erdos3.FiniteProbabilityWeights.complexMean_congr_support
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T10:17:32.191317+00:00
-- url     : https://prove2.me/theorems/bcf12dc9-3523-48fa-a921-dfb5ad89a8f8
-- title:
--   The complex mean of a finite probability weight depends only on its support
-- statement:
--   Let $X$ be a finite type and $p$ a `FiniteProbabilityWeights X` (a structure bundling a weight function $p.\mathrm{weight} : X\to\mathbb{R}$ with nonnegative values summing to $1$). Let $f,g : X\to\mathbb{C}$ satisfy $f(x)=g(x)$ for every $x$ with $p.\mathrm{weight}(x)\ne 0$. Then `p.complexMean f = p.complexMean g`, where `p.complexMean v` is $\sum_{x\in X} p.\mathrm{weight}(x)\,v(x)$.
--
--   Lean: `OAI.Erdos3.FiniteProbabilityWeights.complexMean_congr_support` in `lean/OAI/Combinatorics/Progressions/Estimates/FiniteFiberTest.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B001` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/FiniteFiberTest.lean#L191

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B001

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

namespace FiniteProbabilityWeights

variable (p : FiniteProbabilityWeights Ω) (G : Finset Ω)

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

theorem complexMean_congr_support {f g : X → ℂ}
    (h : ∀ x, p.weight x ≠ 0 → f x = g x) : p.complexMean f = p.complexMean g := by
  sorry

end Erdos3.FiniteProbabilityWeights
end
end OAI
