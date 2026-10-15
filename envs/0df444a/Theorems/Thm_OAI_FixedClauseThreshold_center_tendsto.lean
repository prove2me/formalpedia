-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_center_tendsto
-- name    : OAI.FixedClauseThreshold.center_tendsto
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T05:18:06.470468+00:00
-- url     : https://prove2.me/theorems/49cff249-ffcc-4185-ba6e-200397e8ef0c
-- title:
--   Convergence of the normalized centers of random proper $k$-SAT
-- statement:
--   Fix a clause size $k\ge 3$. Let $\gamma_k(n)$ denote the *normalized center* of the random proper $k$-SAT model on $n$ variables: draw $M=2^{k+1}n$ independent uniformly random proper $k$-clauses $C_1,\dots,C_M$ (each clause uses $k$ distinct variables chosen uniformly among $x_1,\dots,x_n$, with independent fair signs), let the *satisfiable lifetime* $L_n$ be the number of indices $j\in\{1,\dots,M\}$ for which $C_1\wedge\cdots\wedge C_j$ is satisfiable, and set $\gamma_k(n)=\mathbb{E}[L_n]/n$.
--
--   **Theorem.** The sequence $(\gamma_k(n))_{n\ge1}$ converges, and its limit equals its limit superior:
--
--   $$
--   \lim_{n\to\infty}\gamma_k(n)=\gamma_k^{*}:=\limsup_{n\to\infty}\gamma_k(n).
--   $$
--
--   The limiting center $\gamma_k^{*}$ is a finite real number, and it is the threshold density in the sharp-threshold statement for random proper $k$-SAT: for densities $c$ below $\gamma_k^{*}$ a random formula with $\lfloor cn\rfloor$ clauses is satisfiable with probability tending to $1$, and above it with probability tending to $0$.
--
--   **Formalization Note** In Lean, $\gamma_k(n)$ is `center n k` and $\gamma_k^{*}$ is `limitingCenter k`, defined as `Filter.limsup (fun n => center n k) Filter.atTop`. The function `center n k` is defined for every $n$; for $n<k$ there are no proper clauses and Lean's conventions (an empty average and division by zero both give $0$) make it $0$, which does not affect the limit.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/Main.lean#L21-L35

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
import Definitions.Def_OAI_Probability_RandomSAT_Transfer
import Definitions.Def_OAI_Probability_RandomSAT_CenterComparison
import Definitions.Def_OAI_Probability_RandomSAT_Convergence
import Definitions.Def_OAI_Probability_RandomSAT_Main

open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable

theorem OAI.FixedClauseThreshold.center_tendsto (k : ℕ) (hk : 3 ≤ k) :
    Filter.Tendsto (fun n : ℕ => center n k) Filter.atTop (nhds (limitingCenter k)) := by sorry
