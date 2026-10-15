-- Prove2me | Theorems.Thm_OAI_BufferedIsing_normalized_ratio_of_rectangles
-- name    : OAI.BufferedIsing.normalized_ratio_of_rectangles
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:15:37.758721+00:00
-- url     : https://prove2.me/theorems/0a4bfe42-e614-49b3-934c-e86346bb095b
-- title:
--   Bounded log cross-ratios control ratios of normalized conditional probabilities
-- statement:
--   Let $A$ be a finite set, $B$ an arbitrary set, and $p:A\times B\to(0,\infty)$ a strictly positive function. Suppose that for some $L\in\mathbb{R}$ all log cross-ratios of $p$ are bounded by $L$:
--
--   $$\bigl|\log p(a,b)+\log p(a',b')-\log p(a,b')-\log p(a',b)\bigr|\le L\qquad\text{for all }a,a'\in A,\ b,b'\in B.$$
--
--   For $b\in B$ let $P(a\mid b)=p(a,b)\big/\sum_{x\in A}p(x,b)$ be the normalized probability of $a$ in the column $b$. Then for every $a\in A$ and all $b,b'\in B$,
--
--   $$e^{-L}\le\frac{P(a\mid b)}{P(a\mid b')}\le e^{L}.$$
--
--   Control of the unnormalized cross-ratios thus bounds the ratio of the actual normalized probabilities, not merely of odds, with the same constant $L$. With $A$ the configurations of a block $I$, $B$ the prescriptions on a block $J$, $p$ the pinned joint weight and $L$ the extreme log-odds, it bounds how much the conditional law of $\sigma_I$ can change when the prescription on $J$ is changed.
--
--   **Formalization Note** $A$ carries a `Fintype` instance and is nonempty because a point $a\in A$ is given; $B$ is an arbitrary type. Both bounds are stated for the quotient of the two normalized probabilities, written with real division.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Ising/Marginals.lean#L100-L141

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

theorem OAI.BufferedIsing.normalized_ratio_of_rectangles {A B : Type*} [Fintype A]
    (p : A → B → ℝ) (hp : ∀ a b, 0 < p a b) (L : ℝ)
    (hrect : ∀ a a' b b',
      |Real.log (p a b) + Real.log (p a' b') - Real.log (p a b') -
        Real.log (p a' b)| ≤ L) (a : A) (b b' : B) :
    Real.exp (-L) ≤ (p a b / ∑ x, p x b) / (p a b' / ∑ x, p x b') ∧
      (p a b / ∑ x, p x b) / (p a b' / ∑ x, p x b') ≤ Real.exp L := by sorry
