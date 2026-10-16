-- Prove2me | Theorems.Thm_OAI_TreeEdit_TorusTree_sampledWord_child_mean
-- name    : OAI.TreeEdit.TorusTree.sampledWord_child_mean
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:59:26.548991+00:00
-- url     : https://prove2.me/theorems/3d4ad3a8-fd0d-4236-acbb-1a51d46f2295
-- title:
--   Shifting one child subtree costs at most $T$ times the child's expected edit cost
-- statement:
--   This compares the average edit cost of a perturbation of one subtree with the average edit cost inside that subtree, for the random tree words used in the lower bound for the $\ell_1$ distortion of edit distance.
--
--   **Configurations.** Fix natural numbers $g, s, L, T$ and put $m = gs$. Let $I$ be a type, $r : I \to \mathbb{N}$, and a map $j : \{0,\dots,g-1\} \to I$. For a permutation $\sigma$ of $I$ let $P(\sigma) = \prod_{v=0}^{g-1} r(\sigma(j(v)))$. A child index $i \in \{0,\dots,m-1\}$ belongs to the group $\gamma(i) = \lfloor i/s \rfloor$; write $p_i(\sigma) = r(\sigma(j(\gamma(i))))$ and, for $z \in \mathbb{Z}/L$ with standard representative $\bar z$, put $c_\sigma(z,i) = 1 + (\bar z \bmod p_i(\sigma))\cdot \lfloor P(\sigma)/p_i(\sigma)\rfloor$. A configuration of depth $0$ is trivial, and a configuration of depth $h+1$ is a tuple $C = (\sigma, (z_i, C_i)_{i<m})$ consisting of a permutation $\sigma$ of $I$, residues $z_i \in \mathbb{Z}/L$ and configurations $C_i$ of depth $h$.
--
--   **States.** For an abelian group $A$ let $\mathcal{S}_0(A) = A$ and $\mathcal{S}_{h+1}(A) = \mathcal{S}_h(A)^m$; an element of $\mathcal{S}_h(A)$ labels the $m^h$ leaves of the complete $m$-ary tree of depth $h$, and addition is coordinatewise. Let $\Delta_h(u) \in \mathcal{S}_h(A)$ be the constant state with every leaf equal to $u$. For $y \in \mathcal{S}_h(A)$ and a child index $i$ let $\iota_i(y) \in \mathcal{S}_{h+1}(A)$ be the state equal to $y$ at child $i$ and to $0$ at all other children.
--
--   **Sampled words.** Let $R \ge 1$ and $M \ge 1$. For $t \in \mathbb{R}/\mathbb{Z}$ with representative $\tilde t \in [0,1)$ put $\mathrm{bin}_R(t) = \lfloor R\tilde t\rfloor \in \{0,\dots,R-1\}$. For a configuration $C$ of depth $h$ and $x \in \mathcal{S}_h(\mathbb{R}/\mathbb{Z})$ the word $w_C(x)$, of length $(mT)^h$, is defined recursively: for $h=0$ it is the one-letter word $\mathrm{bin}_R(x)$; for $C = (\sigma,(z_i,C_i))$ of depth $h+1$ it is the concatenation, over rounds $a = 0,1,\dots,T-1$ and inside each round over $i = 0,\dots,m-1$, of the words $w_{C_i}\big(x_i + \Delta_h(a\,c_\sigma(z_i,i)/P(\sigma))\big)$, each letter being tagged with the child index $i$. For $x \in \mathcal{S}_h(\mathbb{Z}/M)$ the sampled word is $W_C(x) = w_C(x/M)$, where every leaf value $u \in \mathbb{Z}/M$ with standard representative $\bar u \in \{0,\dots,M-1\}$ is sent to $\bar u/M \bmod 1$. Finally $\mathrm{ed}$ denotes the unit-cost edit distance (the least number of single-letter insertions, deletions and substitutions), and $\mathbb{E}_x$ is the average over $x$ uniformly distributed in a finite group.
--
--   **Statement.** Assume $M \ge 1$, $R \ge 1$, $r(v) > 0$ for every $v \in I$ and $P(\sigma) \mid M$ for every permutation $\sigma$ of $I$. Let $C = (\sigma, (z_v, C_v)_{v<m})$ be a configuration of depth $h+1$, let $i < m$ be a child index and let $y \in \mathcal{S}_h(\mathbb{Z}/M)$. Then
--
--   $$
--   \mathbb{E}_{x \in \mathcal{S}_{h+1}(\mathbb{Z}/M)}\, \mathrm{ed}\big(W_C(x),\, W_C(x + \iota_i(y))\big) \le T\; \mathbb{E}_{x' \in \mathcal{S}_{h}(\mathbb{Z}/M)}\, \mathrm{ed}\big(W_{C_i}(x'),\, W_{C_i}(x' + y)\big),
--   $$
--
--   where both averages are over the uniform distribution.
--
--   The subtree below child $i$ contributes one block to each of the $T$ rounds of the word $W_C(x)$, so perturbing only that subtree costs at most $T$ times the expected cost inside the subtree. This is how edit-cost bounds, and the spectral bounds derived from them, pass from a node to its children with the constant multiplied by $T$.
--
--   **Formalization Note** The embedding $\iota_i$ is `child h i` (a `Pi.single`), and the averages are `mean` over `State (ZMod M) (g*s) (h+1)` and `State (ZMod M) (g*s) h`. The type $I$ need not be finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/RandomCircle.lean#L302-L341

import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleTree
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleSeparation
import Definitions.Def_OAI_Combinatorics_TreeEdit_RandomCircle

open OAI OAI.TreeEdit OAI.TreeEdit.TorusTree
open scoped BigOperators
open Classical FiniteProbability

theorem OAI.TreeEdit.TorusTree.sampledWord_child_mean {I : Type} {g s L M T R : ℕ} [NeZero M] [NeZero R]
    (r : I → ℕ) (j : Fin g → I) (hr : ∀ i, 0 < r i)
    (hPM : ∀ σ : Equiv.Perm I, period r j σ ∣ M)
    (h : ℕ) (C : Config I L (g*s) (h+1)) (i : Fin (g*s)) (z : State (ZMod M) (g*s) h) :
    mean (fun x : State (ZMod M) (g*s) (h+1) =>
      (ed (sampledWord r j T R (h+1) C x).val
        (sampledWord r j T R (h+1) C (x + child (A := ZMod M) h i z)).val : ℝ)) ≤
      T * mean (fun x : State (ZMod M) (g*s) h =>
        (ed (sampledWord r j T R h (C.2 i).2 x).val
          (sampledWord r j T R h (C.2 i).2 (x + z)).val : ℝ)) := by sorry
