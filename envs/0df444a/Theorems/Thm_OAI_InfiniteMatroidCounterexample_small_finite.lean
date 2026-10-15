-- Prove2me | Theorems.Thm_OAI_InfiniteMatroidCounterexample_small_finite
-- name    : OAI.InfiniteMatroidCounterexample.small_finite
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:40:29.645981+00:00
-- url     : https://prove2.me/theorems/c0d0b224-4fb3-4b8f-b7dc-bad37e96a0c1
-- title:
--   Finite sets have vanishing block density
-- statement:
--   Let $D$ be the set of pairs $(m,g)$ where $m\in\mathbb N$ and $g:\{0,1\}^m\to\{0,1\}$ is a Boolean function of $m$ variables, and let $E_0=D\times\{0,1\}$. For $m\in\mathbb N$, the $m$-th block $W_m\subseteq E_0$ consists of all elements $((m,g),b)$; it is finite, with $|W_m|=2\cdot 2^{2^m}$. The density of $X\subseteq E_0$ in the $m$-th block is $\delta_m(X)=|X\cap W_m|/|W_m|$, and $X$ is called *small* if $\delta_m(X)\to0$ as $m\to\infty$.
--
--   **Theorem.** Every finite set $X\subseteq E_0$ is small:
--   $$X\ \text{finite}\quad\Longrightarrow\quad \lim_{m\to\infty}\frac{|X\cap W_m|}{|W_m|}=0 .$$
--
--   Small sets form the ideal of negligible sets underlying the whole construction (two sets are in the same class when their symmetric difference is small). This lemma guarantees that finite modifications never leave a class, which is used whenever a basis is changed by exchanging finitely many elements.
--
--   **Formalization Note** `Small X` is `Tendsto (density X) atTop (𝓝 0)`, where `density X m` is the real number `(X ∩ wBlock m).card / (wBlock m).card` computed with `traceFinset`; blocks are nonempty, so no division-by-zero convention is involved.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/InfiniteMatroid/BlockDensity.lean#L196-L208

import Mathlib
import Definitions.Def_InfiniteMatroid
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cardinality
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Ideals
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_OrdinalRank
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_FiniteCounting
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Basic
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_BlockDensity

open OAI OAI.InfiniteMatroidCounterexample
open Set Filter Finset
open scoped Topology symmDiff

theorem OAI.InfiniteMatroidCounterexample.small_finite {X : Set E0} (hX : X.Finite) : Small X := by sorry
