-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_embeddedAverage_alive
-- name    : OAI.FixedClauseThreshold.embeddedAverage_alive
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T05:03:15.941986+00:00
-- url     : https://prove2.me/theorems/c5cbf8d6-3f8d-46da-8cc0-aa5866e5edb9
-- title:
--   Exact one-step survival under a random embedded auxiliary clause
-- statement:
--   Let $n,v,k\in\mathbb N$ with $v\ge1$, and let $e:\{1,\dots,v\}\to\{1,\dots,n\}$ be any map. An *auxiliary $k$-clause* on $v$ variables is an ordered $k$-tuple of literals $C=\big((i_1,b_1),\dots,(i_k,b_k)\big)\in(\{1,\dots,v\}\times\{0,1\})^k$; repeated variables are allowed, so there are $(2v)^k$ of them. Through $e$ it acts on assignments $\sigma\in\{0,1\}^n$ of the variables $x_1,\dots,x_n$: $\sigma$ satisfies the embedded clause $e(C)$ if $\sigma(x_{e(i_j)})=b_j$ for some $j$. For $S\subseteq\{0,1\}^n$ call a variable *forced* if $S\ne\emptyset$ and all members of $S$ agree on it, and let
--
--   $$
--   F_e(S)=\big\{\,i\in\{1,\dots,v\}:\ x_{e(i)}\text{ is forced in }S\,\big\}.
--   $$
--
--   Let $\operatorname{alive}(T)$ be $1$ if $T\ne\emptyset$ and $0$ otherwise. If $C$ is uniform among the auxiliary $k$-clauses, then
--
--   $$
--   \mathbb E_C\Big[\operatorname{alive}\big(S\cap\operatorname{Sat}(e(C))\big)\Big]=\operatorname{alive}(S)\left(1-\Big(\frac{|F_e(S)|}{2v}\Big)^{k}\right).
--   $$
--
--   So a random embedded auxiliary clause destroys a nonempty set $S$ with probability exactly $(|F_e(S)|/2v)^k$, which depends on $S$ only through the number of forced variables seen by $e$. For $e$ the identity this is the one-step survival law $1-(\phi/2)^k$ of the auxiliary clause model, $\phi$ being the fraction of forced variables; for $e$ the inclusion of a block of variables it describes clauses confined to that block, which is how a system is compared with its blocks.
--
--   **Formalization Note** The left side is `embeddedAverage e k alive S`, a uniform mean over `AuxiliaryClause v k`, which is `Fin k → Fin v × Bool`; $F_e(S)$ is `embeddedForced S e`. The assumption $v\ge1$ makes the set of literals nonempty; for $S=\emptyset$ both sides are $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/Interpolation.lean#L203-L227

import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement
import Definitions.Def_OAI_Probability_RandomSAT_FiniteMean
import Definitions.Def_OAI_Probability_RandomSAT_ClauseProcess
import Definitions.Def_OAI_Probability_RandomSAT_Binomial
import Definitions.Def_OAI_Probability_RandomSAT_Forcing
import Definitions.Def_OAI_Probability_RandomSAT_Variance
import Definitions.Def_OAI_Probability_RandomSAT_Concentration
import Definitions.Def_OAI_Probability_RandomSAT_CenterBounds
import Definitions.Def_OAI_Probability_RandomSAT_Interpolation

open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable

theorem OAI.FixedClauseThreshold.embeddedAverage_alive {n v k : ℕ} (hv : 0 < v) (e : Fin v → Fin n)
    (S : Finset (Assignment n)) :
    embeddedAverage e k alive S = alive S *
      (1 - (((embeddedForced S e).card : ℝ) / (2 * v))^k) := by sorry
