-- Prove2me | Theorems.Thm_OAI_BufferedIsing_extreme_rectangle
-- name    : OAI.BufferedIsing.extreme_rectangle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:15:09.581175+00:00
-- url     : https://prove2.me/theorems/92bec51c-5045-4a53-8b58-61a0f28b8971
-- title:
--   Mixed differences over arbitrary rectangles are bounded by the extreme rectangle
-- statement:
--   Let $A$ and $B$ be partially ordered sets, each having a least element $\bot$ and a greatest element $\top$. Let $f:A\times B\to\mathbb{R}$ satisfy the rectangle inequality: for all $u\le v$ in $A$ and all $s\le t$ in $B$,
--
--   $$f(u,t)+f(v,s)\le f(u,s)+f(v,t).$$
--
--   Then for all $a,a'\in A$ and $b,b'\in B$, whether or not they are comparable,
--
--   $$\bigl|f(a,b)+f(a',b')-f(a,b')-f(a',b)\bigr|\le f(\top,\top)+f(\bot,\bot)-f(\top,\bot)-f(\bot,\top).$$
--
--   The hypothesis says that $f$ has nonnegative mixed differences on ordered rectangles, i.e. $f$ is supermodular in its two arguments. The conclusion bounds the mixed difference over any rectangle, ordered or not and with either sign, by the mixed difference over the extreme rectangle $\{\bot,\top\}\times\{\bot,\top\}$. Applied to the logarithm of a positive log-supermodular two-block marginal, it bounds every log cross-ratio by the extreme log-odds.
--
--   **Formalization Note** $A$ and $B$ are types with `PartialOrder` and `BoundedOrder` instances; no lattice structure or finiteness is required.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Ising/Marginals.lean#L57-L75

import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic
import Definitions.Def_OAI_Probability_Ising_Colorings
import Definitions.Def_OAI_Probability_Ising_EdwardsSokal
import Definitions.Def_OAI_Probability_Ising_TwoSpin
import Definitions.Def_OAI_Probability_Ising_SpinCorrelation
import Definitions.Def_OAI_Probability_Ising_Marginals

open OAI OAI.BufferedIsing
open scoped BigOperators Classical

theorem OAI.BufferedIsing.extreme_rectangle {A B : Type*} [PartialOrder A] [BoundedOrder A]
    [PartialOrder B] [BoundedOrder B] (f : A → B → ℝ)
    (hrect : ∀ u v s t, u ≤ v → s ≤ t → f u t + f v s ≤ f u s + f v t)
    (a a' : A) (b b' : B) :
    |f a b + f a' b' - f a b' - f a' b| ≤
      f ⊤ ⊤ + f ⊥ ⊥ - f ⊤ ⊥ - f ⊥ ⊤ := by sorry
