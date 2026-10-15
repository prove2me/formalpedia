-- Prove2me | Theorems.Thm_OAI_DiscreteFree_GraphProducer_exists_rare_component
-- name    : OAI.DiscreteFree.GraphProducer.exists_rare_component
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-15T10:14:09.288386+00:00
-- url     : https://prove2.me/theorems/3c37ca29-83f4-4667-a8b8-0c174a6898db
-- title:
--   Some level of the all-colorings Cayley graph sequence has rare non-good roots
-- statement:
--   Let $A$ be a finite alphabet and let $\mathcal P=A\times\{+,-\}$ be the set of *ports*, with $d=|\mathcal P|=2|A|$. The reverse of a port is $\overline{(a,\pm)}=(a,\mp)$, and the ports $(a,+)$ and $(a,-)$ stand for the letters $a$ and $a^{-1}$ of the free group $F(A)$. For $N\in\mathbb N$ let $B_N\subseteq F(A)$ be the ball of reduced words of length at most $N$, let $G_N=\mathrm{Sym}(B_N)$ be the group of permutations of $B_N$, and let $\rho_N\colon F(A)\to G_N$ be a fixed homomorphism sending each generator $a$ to a permutation of $B_N$ that agrees with left multiplication $g\mapsto ag$ whenever $|ag|\le N$. Let $C$ be a finite nonempty set of colors and put $k=|C|$.
--
--   The *all-colorings sequence graph* has vertex set $\mathcal V=\bigsqcup_{N\ge0}C^{G_N}\times G_N$. A vertex $(N,c,x)$ consists of a level $N$, a coloring $c\colon G_N\to C$ and a root $x\in G_N$, and its color is $c(x)$. The port $e$ moves $(N,c,x)$ to $(N,c,x\,\rho_N(e))$, where $\rho_N(e)$ is the image of the letter of $e$. The coloring and the level never change. A word of ports $w=(e_1,\dots,e_n)$ is *reduced* if $e_{i+1}\ne\overline{e_i}$ for all $i$. Walking along $w$ from $v_0=v$ produces the vertices $v_1,\dots,v_n$, where $v_i$ is obtained from $v_{i-1}$ through the port $e_i$.
--
--   Let $S$ be a finite set of *states*, and let $\mathrm{compat}\subseteq\mathcal V\times S$ and $\mathrm{trans}\subseteq S\times S$ be arbitrary relations. A triple $(v,j,w)$ with $w$ of length $n$ is *matched* if there are states $j_0=j,j_1,\dots,j_n$ with $\mathrm{trans}(j_{i-1},j_i)$ for $1\le i\le n$ and $\mathrm{compat}(v_i,j_i)$ for $0\le i\le n$. A vertex $v$ is *$n$-good* if no state $j$ and no reduced port word $w$ of length exactly $n$ make $(v,j,w)$ matched.
--
--   **Theorem.** Let $Q,H,V\in\mathbb N$ with $Q\ge1$, $H\ge1$ and $d\ge1$, and assume $2dQH<k$. Let $P$ assign to every state $j\in S$ a set of colors $P(j)\subseteq C$ with $|P(j)|\le H$, and assume that
--
--   1. $\mathrm{compat}(v,j)$ implies that the color of $v$ lies in $P(j)$, for all $v\in\mathcal V$ and $j\in S$;
--   2. every state has at most $Q$ successors: $|\{j'\in S:\mathrm{trans}(j,j')\}|\le Q$ for all $j\in S$.
--
--   Then there is a level $n\ge2$ such that
--
--   $$
--   20V\cdot\#\bigl\{(c,x)\in C^{G_n}\times G_n:\ (n,c,x)\ \text{is not}\ n\text{-good}\bigr\}\;<\;\bigl|C^{G_n}\times G_n\bigr|.
--   $$
--
--   So at a suitable level $n$, where the walk length in the goodness test equals the level, fewer than a $1/(20V)$ fraction of the rooted colorings fail to be $n$-good.
--
--   This is the counting input of the metric block construction. The rooted colorings of level $n$ become vertices of a metric block, and the estimate makes the non-good vertices, which carry matched reduced walks of length $n$, too rare to spoil an averaging argument over all directed edges.
--
--   **Formalization Note** Ports are `A × Bool`, so $d$ appears as `Nat.card (A × Bool)`, and the hypothesis $d\ge1$ says that $A$ is nonempty. The homomorphism $\rho_N$ is `ballRep`, obtained from `FreeGroup.lift` and permutations chosen to extend the partial left translations. The vertex set is `GraphProducer.Vertex A C`, goodness is `PortGraph.Good` for `sequenceGraph A C`, and level-$n$ pairs enter it through `intoSequence`. Cardinalities are `Nat.card`. The constant $V$ is an arbitrary natural number, and for $V=0$ the claim is trivial.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/GraphSequence.lean#L17-L63

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
variable (A C S : Type*) [Fintype A] [DecidableEq A] [Fintype C] [Nonempty C] [Fintype S]

theorem OAI.DiscreteFree.GraphProducer.exists_rare_component (Q H V : ℕ) (hQpos : 0 < Q) (hHpos : 0 < H)
    (hDpos : 0 < Nat.card (A × Bool))
    (hk : 2 * Nat.card (A × Bool) * Q * H < Nat.card C)
    (compatible : Vertex A C → S → Prop) (trans : S → S → Prop) (P : S → Finset C)
    (hP : ∀ j, (P j).card ≤ H)
    (hcolor : ∀ z j, compatible z j → sequenceColor A C z ∈ P j)
    (hQ : ∀ j, Fintype.card {k : S // trans j k} ≤ Q) :
    ∃ n : ℕ, 2 ≤ n ∧
      20 * V * Nat.card {z : (Cayley A n → C) × Cayley A n //
        ¬ (sequenceGraph A C).Good compatible trans n (intoSequence A C n z)} <
      Nat.card ((Cayley A n → C) × Cayley A n) := by sorry
