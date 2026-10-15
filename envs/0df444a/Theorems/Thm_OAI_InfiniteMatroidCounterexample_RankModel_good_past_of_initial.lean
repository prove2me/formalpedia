-- Prove2me | Theorems.Thm_OAI_InfiniteMatroidCounterexample_RankModel_good_past_of_initial
-- name    : OAI.InfiniteMatroidCounterexample.RankModel.good_past_of_initial
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:46:28.169361+00:00
-- url     : https://prove2.me/theorems/214d4abf-16e5-4f58-aaaf-5a16e588dda4
-- title:
--   Goodness of prototype families passes to the union of all earlier stages
-- statement:
--   Let $D$ be the set of pairs $(m,g)$ with $m\in\mathbb N$ and $g:\{0,1\}^m\to\{0,1\}$, let $E_0=D\times\{0,1\}$, and call $X\subseteq E_0$ *small* if its density in the $m$-th block $\{((m,g),b)\}$ tends to $0$. Let $\mathfrak c$ be the initial ordinal of the continuum, regarded as a well-ordered index set. Let $R$ be a rank model on $D$: an ideal of subsets of $D$, an ultrafilter $\mathcal U$ on $D$ containing no set of that ideal, and a rank function $\rho$ from subsets of $D$ to $\mathfrak c$ (antitone modulo the ideal on sets in $\mathcal U$, and satisfying a thinning property). For $X\subseteq E_0$ let $X_0=\{d:(d,0)\in X\}$ and $X_1=\{d:(d,1)\in X\}$; $X$ is *$R$-admissible* if either $X_0\in\mathcal U$, $D\setminus X_1\in\mathcal U$ and $\rho(D\setminus X_1)<\rho(X_0)$, or $X_0\notin\mathcal U$, $D\setminus X_1\notin\mathcal U$ and $\rho(X_1)<\rho(D\setminus X_0)$.
--
--   A *prototype* is a pair $p=(T_p,s_p)$ with $T_p\subseteq E_0$ and $s_p\in\{0,1\}$; its flip is $\bar p=(E_0\setminus T_p,1-s_p)$. A set $P$ of prototypes is *good* if every $T_p$ ($p\in P$) is $R$-admissible, $\bar p\in P$ for every $p\in P$, and $T_p\setminus T_q$ is not small for all distinct $p,q\in P$. Let $f$ assign to each $b\in\mathfrak c$ either nothing or a set $f(b)\subseteq E_0$; put $\sigma(\text{nothing})=\emptyset$, $\sigma(B)=\{(B,0),(E_0\setminus B,1)\}$, and
--   $$\mathrm{Past}_f(a)=\bigcup_{b<a}\sigma(f(b)),\qquad \mathrm{Init}_f(a)=\mathrm{Past}_f(a)\cup\sigma(f(a)).$$
--
--   **Theorem.** For every rank model $R$ on $D$, every such $f$ and every $a\in\mathfrak c$,
--   $$\bigl(\mathrm{Init}_f(b)\ \text{is good for every } b<a\bigr)\quad\Longrightarrow\quad \mathrm{Past}_f(a)\ \text{is good}.$$
--
--   This is the inductive step of the transfinite recursion that assembles the prototypes: at stage $a$ the construction adds a new complementary pair only when $\mathrm{Past}_f(a)$ is good, and this lemma shows that goodness of all earlier initial families (in particular at limit stages) is inherited by their union.
--
--   **Formalization Note** The index type is `CIndex = Cardinal.continuum.ord.ToType`, $f$ is a map `CIndex → Option (Set E0)` (`none` for an empty stage), and goodness is the structure `R.GoodPrototypes` with fields `admissible`, `flip_closed` and `separated`. No assumption on the ideal of `R` is needed here.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/InfiniteMatroid/TransfiniteConstruction.lean#L63-L78

import Mathlib
import Definitions.Def_InfiniteMatroid
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cardinality
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Ideals
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_OrdinalRank
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_FiniteCounting
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Basic
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_BlockDensity
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Columns
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cesaro
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_ProbeLimits
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_SparsePerturbation
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Interpolation
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_LocalBases
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_DensityIdeal
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Reservations
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_BasisExtension
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Zones
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Separation
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Prototype
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_PrototypeExtension
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Matroid
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_TransfiniteConstruction

open OAI OAI.InfiniteMatroidCounterexample OAI.InfiniteMatroidCounterexample.RankModel
open Set Filter
open scoped Topology symmDiff
variable (R : RankModel D)

theorem OAI.InfiniteMatroidCounterexample.RankModel.good_past_of_initial (f : CIndex → Option (Set E0)) (a : CIndex)
    (h : ∀ b < a, R.GoodPrototypes (initialPrototypes f b)) :
    R.GoodPrototypes (pastPrototypes f a) := by sorry
