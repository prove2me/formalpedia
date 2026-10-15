-- Prove2me | Theorems.Thm_OAI_ThorpCompatibility_gridAllowed_iff_rank
-- name    : OAI.ThorpCompatibility.gridAllowed_iff_rank
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T23:54:30.719566+00:00
-- url     : https://prove2.me/theorems/f930a411-b8d3-458f-9d48-f619a862246d
-- title:
--   In a compatible grid, a value is excluded exactly when its producing column is exposed earlier
-- statement:
--   Fix $A,D\in\mathbb N$, write $[m]=\{0,1,\dots,m-1\}$ and let $S_m$ be the group of permutations of $[m]$. Let $(r,c)$ be a grid, consisting of row permutations $r_h\in S_D$ for $h\in[A]$ and column permutations $c_l\in S_A$ for $l\in[D]$, and assume it is *compatible*: for every $j\in[D]$ the map $\pi_j:h\mapsto c_{r_h(j)}(h)$ is injective, hence a permutation of $[A]$. For $j\in[D]$ and $w\in[A]$ let
--   $$
--   \mathrm{col}_j(w)=r_{\pi_j^{-1}(w)}(j)
--   $$
--   be the column through which the value $w$ is produced at position $j$.
--
--   Let $e\in S_D$ be an exposure order on the columns (column $l$ is exposed before column $k$ when $e(l)<e(k)$). Fix a column $k\in[D]$ and a row $i\in[A]$, and put $j=r_i^{-1}(k)$. Given the rows $r$ and the columns exposed before $k$, a value $w\in[A]$ is *allowed* for the entry $c_k(i)$ if there is no row $h\in[A]$ whose column $l=r_h(j)$ is exposed before $k$ and already satisfies $c_l(h)=w$. Then for every $w\in[A]$,
--
--   $$
--   w\ \text{is allowed for the entry } c_k(i)\quad\Longleftrightarrow\quad e(k)\le e\big(\mathrm{col}_j(w)\big),\qquad j=r_i^{-1}(k).
--   $$
--
--   So, in a compatible grid, a value is excluded exactly when the column that actually produces it at position $j$ is exposed strictly before column $k$. This turns the combinatorial exclusion rule into a comparison of the ranks of two columns in the order $e$, so that for a uniformly random exposure order the exclusion probabilities can be computed from rank statistics of a random permutation.
--
--   **Formalization Note** The predicate `gridAllowed k i y w` is defined for an abstract past `y`; here it is evaluated at `gridPast e k i a`, which consists of the rows, the columns exposed before $k$ (as `Option` values, `none` for columns not yet exposed) and the entries of column $k$ above row $i$; the last component plays no role in the predicate. The permutation $\pi_j$ is `outputEquiv a ha j` and $\mathrm{col}_j$ is `columnFor a ha j`; both require the compatibility proof `ha`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/GridExposure.lean#L51-L70

import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_LightRescaling
import Definitions.Def_OAI_Probability_ThorpCompatibility_Prediction
import Definitions.Def_OAI_Probability_ThorpCompatibility_RankLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Model
import Definitions.Def_OAI_Probability_ThorpCompatibility_EntropyChain
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridExposure

open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset

theorem OAI.ThorpCompatibility.gridAllowed_iff_rank {A D : ℕ} (a : Grid A D) (ha : Compatible a.1 a.2)
    (e : Equiv.Perm (Fin D)) (k : Fin D) (i : Fin A) (w : Fin A) :
    gridAllowed k i (gridPast e k i a) w ↔ e k ≤ e (columnFor a ha ((a.1 i).symm k) w) := by sorry
