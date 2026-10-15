-- Prove2me | Theorems.Thm_OAI_DiscreteFree_GraphProducer_rare_matched_bound
-- name    : OAI.DiscreteFree.GraphProducer.rare_matched_bound
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-15T10:13:07.004987+00:00
-- url     : https://prove2.me/theorems/c3b7607f-8faa-4ca1-94de-af9ba1535e8d
-- title:
--   Few coloured vertices of the all-colourings Cayley graph admit a matched reduced walk
-- statement:
--   **Setting.** Let $A$ be a finite alphabet, $C$ a finite set of colours and $S$ a finite set of states, and let $n,N,Q,H\in\mathbb{N}$ with $n\le N$. Let $F(A)$ be the free group on $A$, $B_N=\{g\in F(A):\ |g|\le N\}$ the ball of radius $N$ for the word length, and $\Gamma_N=\mathrm{Sym}(B_N)$ its finite permutation group. For each $a\in A$ fix a permutation $\sigma_a$ of $B_N$ with $\sigma_a(g)=ag$ whenever $|ag|\le N$, and let $\rho_N:F(A)\to\Gamma_N$ be the homomorphism with $\rho_N(a)=\sigma_a$. The *Cayley port graph* of $\Gamma_N$ has the ports $(a,\pm)$, $a\in A$, moves $\gamma\cdot(a,\pm)=\gamma\,\rho_N(a^{\pm1})$, and port reversal $(a,\pm)\mapsto(a,\mp)$. The *all-colourings graph* $\mathcal G_N$ has vertex set $V_N=C^{\Gamma_N}\times\Gamma_N$, consisting of pairs $z=(c,\gamma)$ of a colouring of $\Gamma_N$ and a root, with moves $(c,\gamma)\cdot e=(c,\gamma\cdot e)$; it is a disjoint union of copies of the Cayley graph, one for each colouring.
--
--   Let $\kappa\subseteq V_N\times S$ be a compatibility relation, $\tau\subseteq S\times S$ a transition relation, and $P(j)\subseteq C$ a set of colours for each state $j$, such that
--
--   1. $|P(j)|\le H$ for every state $j$;
--   2. if $\kappa((c,\gamma),j)$ holds then $c(\gamma)\in P(j)$;
--   3. every state has at most $Q$ successors: $\#\{k\in S:\ \tau(j,k)\}\le Q$ for every $j$.
--
--   A word $e_1\cdots e_m$ of ports is *reduced* if $e_{i+1}$ is never the reversal of $e_i$. The walk from $z$ along $w$ is *matched* from a state $j$ if $\kappa(z,j)$ holds and, when $w=e\,w'$ is nonempty, there is a state $k$ with $\tau(j,k)$ such that the walk from $z\cdot e$ along $w'$ is matched from $k$. A vertex $z$ is *$n$-good* if no reduced word of length $n$ has a walk from $z$ that is matched from some state.
--
--   **Theorem.**
--   $$
--   \#\{z\in V_N:\ z\text{ is not }n\text{-good}\}\cdot|C|^{n+1}\ \le\ (2|A|)^n\cdot\bigl(|S|\,Q^n\bigr)\cdot H^{n+1}\cdot|V_N| .
--   $$
--
--   Thus the proportion of vertices of $\mathcal G_N$ from which some reduced walk of length $n$ can be matched is at most $(2|A|)^n\,|S|\,Q^n\,(H/|C|)^{n+1}$, which is small when the number of colours is large compared with the other parameters. This is how one finds a finite graph in which almost every vertex is good, as required by the averaging argument of the finite-rank obstruction.
--
--   **Formalization Note** $\Gamma_N$ is `Cayley A N`, $\mathcal G_N$ is `allColoringsGraph A C N`, goodness is `PortGraph.Good`, and the counts on both sides are `Nat.card`; the factor $2|A|$ appears as `Nat.card (A × Bool)`. The successor bound is stated with `Fintype.card` of the subtype of successors.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/GraphColoring.lean#L20-L75

import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
import Definitions.Def_OAI_Analysis_LipschitzFree_Model
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment
import Definitions.Def_OAI_Analysis_LipschitzFree_Words
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths
import Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphWalks
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation
import Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates
import Definitions.Def_OAI_Analysis_LipschitzFree_AffineWeights
import Definitions.Def_OAI_Analysis_LipschitzFree_LabelBumps
import Definitions.Def_OAI_Analysis_LipschitzFree_ScalarTests
import Definitions.Def_OAI_Analysis_LipschitzFree_FiniteQuotients
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphGirth
import Definitions.Def_OAI_Analysis_LipschitzFree_ColorCounting
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphColoring

open OAI OAI.DiscreteFree OAI.DiscreteFree.GraphProducer
open scoped BigOperators ENNReal
open scoped Classical
variable (A : Type*) [Fintype A] [DecidableEq A]
    (C S : Type*) [Fintype C] [Fintype S]

theorem OAI.DiscreteFree.GraphProducer.rare_matched_bound (n N Q H : ℕ) (hnN : n ≤ N)
    (compatible : ((Cayley A N → C) × Cayley A N) → S → Prop)
    (trans : S → S → Prop) (P : S → Finset C)
    (hP : ∀ j, (P j).card ≤ H)
    (hcolor : ∀ z j, compatible z j → z.1 z.2 ∈ P j)
    (hQ : ∀ j, Fintype.card {k : S // trans j k} ≤ Q) :
    Nat.card {z : (Cayley A N → C) × Cayley A N //
        ¬ (allColoringsGraph A C N).Good compatible trans n z} * Nat.card C ^ (n+1) ≤
      Nat.card (A × Bool) ^ n * (Nat.card S * Q ^ n) * H ^ (n+1) *
        Nat.card ((Cayley A N → C) × Cayley A N) := by sorry
