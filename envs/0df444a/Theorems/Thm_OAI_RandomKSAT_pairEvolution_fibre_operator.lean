-- Prove2me | Theorems.Thm_OAI_RandomKSAT_pairEvolution_fibre_operator
-- name    : OAI.RandomKSAT.pairEvolution_fibre_operator
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T18:06:46.003608+00:00
-- url     : https://prove2.me/theorems/1fb85d30-1fa8-4968-90a2-3bf2b6cee7a1
-- title:
--   The fibre of the refreshed pair chain evolves as a scheduled clause chain
-- statement:
--   Write $[m]=\{0,\dots,m-1\}$ and $\{0,1\}$ for the Booleans. For integers $s,u\ge 0$, an *$s$-clause on $[u]$* is a pair $c=(V,\sigma)$ with $V\subseteq[u]$, $|V|=s$, and signs $\sigma:V\to\{0,1\}$; an assignment $b\in\{0,1\}^u$ *satisfies* $c$ if $b_v=\sigma_v$ for some $v\in V$, and $\mathrm{Sat}(c)$ denotes the set of such $b$. Let $\mathcal C_{u,s}$ be the finite set of $s$-clauses on $[u]$.
--
--   Fix natural numbers $k\le u$. Variables are split into $k$ *root* variables and $u$ *outer* variables. A *root pattern* is a map $t:[k]\to\{0,1,\bot\}$ of size $|t|=\#\{j: t(j)\neq\bot\}$; it is *satisfied* by $x\in\{0,1\}^k$ if $t(j)=x_j$ for some $j$. A *root datum* is a pair $p=(t,c)$ of a root pattern $t$ and an outer clause $c\in\mathcal C_{u,k-|t|}$; a pair $(x,b)\in\{0,1\}^k\times\{0,1\}^u$ *satisfies* $p$ if $t$ is satisfied by $x$ or $b\in\mathrm{Sat}(c)$. We write $\mathrm{Sat}(p)$ for the set of such pairs and $\mathcal R_{u,k}$ for the finite set of all root data.
--
--   Fix a root assignment $a\in\{0,1\}^k$. *Refresh noise* is a tuple $z=(z_\star,(z_j)_{j\in[k]})$ with $z_\star\in\mathcal C_{u,k}$ and $z_j\in\mathcal C_{u,k-1}$. The *refreshed datum* $\rho_a(p,z)=(t,c')$ keeps the root pattern of $p=(t,c)$ and replaces its outer clause by $c'=z_\star$ if $|t|=0$, by $c'=z_j$ if $|t|=1$ and the unique root $j$ of $t$ is satisfied by $a$ (that is, $t(j)=a_j$), and keeps $c'=c$ otherwise.
--
--   Let $(p_i)_{i\in\mathbb N}$ be an environment of root data, $p_i=(t_i,c_i)$. Step $i$ of the *refreshed pair chain* sends a set $S\subseteq\{0,1\}^k\times\{0,1\}^u$ to $S\cap\mathrm{Sat}(\rho_a(p_i,z))$, where $z$ is uniform refresh noise. For such $S$ let $S_a=\{b:(a,b)\in S\}$ be its fibre over $a$, and let $D_i=\{b:(a,b)\in\mathrm{Sat}(p_i)\}$.
--
--   **Theorem.** For every function $f$ from subsets of $\{0,1\}^u$ to $\mathbb R$, every $i\in\mathbb N$ and every $S$,
--
--   $$
--   \mathbb E_{z}\Big[f\big((S\cap \mathrm{Sat}(\rho_a(p_i,z)))_a\big)\Big]=
--   \begin{cases}
--   \mathbb E_{c}\big[f(S_a\cap\mathrm{Sat}(c))\big], & |t_i|=0,\\
--   f(S_a\cap D_i), & |t_i|\neq 0,
--   \end{cases}
--   $$
--
--   where $z$ is uniform on $\mathcal C_{u,k}\times(\mathcal C_{u,k-1})^{[k]}$ and $c$ is uniform on $\mathcal C_{u,k}$.
--
--   Thus, seen through the fibre over $a$, the pair chain is a scheduled chain on subsets of $\{0,1\}^u$: at steps whose environment datum misses the roots, the fibre is intersected with the satisfying set of a fresh uniform $k$-clause, and at all other steps it is intersected with the deterministic mask $D_i$. This allows potential and drift estimates proved for scheduled clause chains to be transferred to the pair chain.
--
--   **Formalization Note** The left side is `uniformStep (pairEvolution a env) i (fun T => f (fibre a T)) S` and the right side is `scheduledStep u k ordinary mask i f (fibre a S)`, where `ordinary i` means $|t_i|=0$ and `mask i` is $D_i$ (`dataMask`). Averages are uniform averages `favg` over finite types; $k\le u$ makes the clause sets nonempty, and $k-1$ is natural-number subtraction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/PairEvolution.lean#L97-L115

import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiniteVariance
import Definitions.Def_OAI_Probability_SATVariance_LifetimePotential
import Definitions.Def_OAI_Probability_SATVariance_RootDisintegration__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiberRefresh
import Definitions.Def_OAI_Probability_SATVariance_PairEvolution

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.pairEvolution_fibre_operator {u k : ℕ} (hku : k ≤ u) (a : Assignment k)
    (env : ℕ → RootData u k) (i : ℕ) (f : Finset (Assignment u) → ℝ) (S : PairState u k) :
    uniformStep (pairEvolution a env) i (fun T => f (fibre a T)) S =
      scheduledStep u k (fun i => rootSize (env i).1 = 0) (fun i => dataMask (env i) a) i f (fibre a S) := by sorry
