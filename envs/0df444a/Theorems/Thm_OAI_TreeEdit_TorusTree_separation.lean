-- Prove2me | Theorems.Thm_OAI_TreeEdit_TorusTree_separation
-- name    : OAI.TreeEdit.TorusTree.separation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:54:14.732557+00:00
-- url     : https://prove2.me/theorems/00e2fcf3-6866-4c06-9e40-34e119aa7c0b
-- title:
--   Separation: shifting a state by a good point makes the tree words differ in a $128^{-h}$ fraction of their length
-- statement:
--   Let $\mathbb T=\mathbb R/\mathbb Z$, with $\|t\|$ the distance from $t$ to $0$, and for $u\in\mathbb N$, $n\ge1$ write $u/n$ also for its image in $\mathbb T$. For finite words $u,v$ let $\operatorname{lcs}(u,v)$ be the length of a longest common subsequence and $\operatorname{def}(u,v)=|u|-\operatorname{lcs}(u,v)$ the deficit.
--
--   **Data.** Let $g,s,L,T,R$ be natural numbers with $m=gs\ge4$, $T\ge1$ and $R\ge1$; let $(r_v)_{v\in I}$ be positive integers indexed by a set $I$, and $j\colon\{0,\dots,g-1\}\to I$ any map. For a permutation $\sigma$ of $I$ let $P_\sigma=\prod_{u<g}r_{\sigma(j(u))}$, for a child $i<m$ let $\gamma(i)=\lfloor i/s\rfloor$ be its group and $p_{\sigma,i}=r_{\sigma(j(\gamma(i)))}$ its factor, and for $z\in\mathbb Z/L\mathbb Z$ with standard representative $\bar z\in\mathbb N$ let $c_\sigma(z,i)=1+(\bar z\bmod p_{\sigma,i})\,P_\sigma/p_{\sigma,i}$.
--
--   **Configurations and goodness.** $\mathcal C_0=\{\ast\}$ and $\mathcal C_{h+1}=\mathrm{Sym}(I)\times(\mathbb Z/L\mathbb Z\times\mathcal C_h)^m$. With $\varepsilon=1/R$: the configuration of depth $0$ is good for $t$ iff $1/R\le\|t\|$, and $(\sigma,(z_i,C_i)_{i<m})$ is good for $t$ iff for every $a\in\{0,\dots,P_\sigma-1\}$ at least $m/64$ children $i$ have $C_i$ good for $t+a\,c_\sigma(z_i,i)/P_\sigma$.
--
--   **States and words.** A state of depth $h$ assigns a point of $\mathbb T$ to every leaf of the complete $m$-ary tree of depth $h$: $\mathcal S_0=\mathbb T$ and $\mathcal S_{h+1}=(\mathcal S_h)^m$, an abelian group under leafwise addition; $\Delta_h(t)\in\mathcal S_h$ is the state with all leaves equal to $t$. For $x\in\mathbb T$ with representative $\{x\}\in[0,1)$ let $\operatorname{bin}_R(x)=\lfloor R\{x\}\rfloor\in\{0,\dots,R-1\}$. The alphabets are $\Sigma_0=\{0,\dots,R-1\}$ and $\Sigma_{h+1}=\{0,\dots,m-1\}\times\Sigma_h$. The tree word $w_h(C,x)$ of a configuration $C\in\mathcal C_h$ and state $x\in\mathcal S_h$ is the word over $\Sigma_h$ defined by: $w_0(\ast,x)$ is the one-letter word $\operatorname{bin}_R(x)$, and for $C=(\sigma,(z_i,C_i)_{i<m})$
--   $$w_{h+1}(C,x)=\prod_{a=0}^{T-1}\ \prod_{i=0}^{m-1}\ i\otimes w_h\Bigl(C_i,\ x_i+\Delta_h\bigl(a\,c_\sigma(z_i,i)/P_\sigma\bigr)\Bigr),$$
--   where products are concatenations in increasing order and $i\otimes w$ tags each letter of $w$ with $i$. Its length is $n_h=(mT)^h$ (so $n_0=1$ and $n_{h+1}=T\,m\,n_h$).
--
--   **Statement.** If $C\in\mathcal C_h$ is good for $t\in\mathbb T$, then for every state $x\in\mathcal S_h$
--
--   $$
--   n_h\ \le\ 128^{h}\cdot\operatorname{def}\Bigl(w_h(C,x),\ w_h\bigl(C,\,x+\Delta_h(t)\bigr)\Bigr).
--   $$
--
--   Thus translating all leaves by a good point $t$ changes the tree word so much that a longest common subsequence misses at least a $128^{-h}$ fraction of its $n_h$ letters. Combined with the fact that random configurations are good with high probability, this is the separation half of the lower bound for the $\ell_1$-distortion of edit distance.
--
--   **Formalization Note** $\mathbb T$ is `UnitAddCircle`, configurations are `Config I L (g * s) h`, goodness is `Good (R : ℝ)⁻¹ r j h C t`, states are `State UnitAddCircle (g * s) h`, $\Delta_h$ is `diagonal h`, the words are `word r j T R h C x : Word (Symbol (g * s) R h) (FiniteTree.length (g * s) T h)` with the tagged concatenation given by `Words.cycles`, and $n_h$ is `FiniteTree.length (g * s) T h`. $\bar z$ is `z.val`; $L=0$ is allowed, in which case $\mathbb Z/0\mathbb Z=\mathbb Z$ and $\bar z=|z|$. The quotient $P_\sigma/p_{\sigma,i}$ is natural-number division, exact here.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/CircleSeparation.lean#L103-L177

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

open OAI OAI.TreeEdit OAI.TreeEdit.TorusTree
open scoped BigOperators
open Classical

theorem OAI.TreeEdit.TorusTree.separation {I : Type} {g s L T R h : ℕ} [NeZero R]
    {r : I → ℕ} {j : Fin g → I} (hr : ∀ i, 0 < r i) (hm : 4 ≤ g * s) (hT : 0 < T)
    (C : Config I L (g * s) h) (x : State UnitAddCircle (g * s) h) (t : UnitAddCircle)
    (ht : Good (R : ℝ)⁻¹ r j h C t) :
    (FiniteTree.length (g * s) T h : ℝ) ≤ (128 : ℝ) ^ h *
      (deficit (word r j T R h C x).val (word r j T R h C (x + diagonal (A := UnitAddCircle) (m := g * s) h t)).val : ℝ) := by sorry
