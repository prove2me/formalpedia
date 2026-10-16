-- Prove2me | Theorems.Thm_OAI_TreeEdit_TorusTree_good_probability
-- name    : OAI.TreeEdit.TorusTree.good_probability
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:53:13.700987+00:00
-- url     : https://prove2.me/theorems/2f27e1b1-f515-49dc-b22e-4f762e16c432
-- title:
--   Random circle-tree configurations are good for a fixed shift with probability at least $9/10$
-- statement:
--   This statement concerns the random configurations used to build tree-structured words from points of the circle $\mathbb T=\mathbb R/\mathbb Z$. For $t\in\mathbb T$ let $\|t\|$ be the distance from $t$ to $0$ in $\mathbb T$, and for $u\in\mathbb N$ and $n\ge1$ write $u/n$ also for its image in $\mathbb T$. Probabilities are for the uniform distribution on the indicated finite set.
--
--   **Data.** Let $I$ be a finite set and $(r_v)_{v\in I}$ a family of pairwise distinct primes with $r_v\ge10$. Let $U\ge1$ be an integer with $r_v\le U$ for all $v$, and $L\ge1$ an integer divisible by every $r_v$. Let $k,s$ be natural numbers, put $g=16k$ and $m=gs=16ks$, and let $j\colon\{0,\dots,g-1\}\to I$ be injective. Let $\varepsilon$ be a real number such that
--   $$2\varepsilon r_v<1\ \ (v\in I),\qquad 2\varepsilon\,(U^{k})^{2}<1,\qquad \frac{16k}{|I|}+U^{16k}\Bigl(\frac45\Bigr)^{ks}\le\frac1{10}.$$
--
--   **Coefficients.** For a permutation $\sigma$ of $I$ let $P_\sigma=\prod_{u=0}^{g-1}r_{\sigma(j(u))}$. Child $i\in\{0,\dots,m-1\}$ lies in group $\gamma(i)=\lfloor i/s\rfloor$ and carries the prime $p_{\sigma,i}=r_{\sigma(j(\gamma(i)))}$. For $z\in\mathbb Z/L\mathbb Z$ with representative $\bar z\in\{0,\dots,L-1\}$ put $c_\sigma(z,i)=1+(\bar z\bmod p_{\sigma,i})\,P_\sigma/p_{\sigma,i}$.
--
--   **Configurations and goodness.** Let $\mathcal C_0=\{\ast\}$ and $\mathcal C_{h+1}=\mathrm{Sym}(I)\times(\mathbb Z/L\mathbb Z\times\mathcal C_h)^m$, so a configuration of depth $h+1$ is a permutation $\sigma$ together with a residue $z_i$ and a configuration $C_i$ of depth $h$ for every child $i<m$. The configuration of depth $0$ is good for $t$ iff $\varepsilon\le\|t\|$, and $(\sigma,(z_i,C_i)_{i<m})$ is good for $t$ iff for every $a\in\{0,\dots,P_\sigma-1\}$ at least a $1/64$ fraction of the children are good at the shifted points:
--   $$m\le64\cdot\#\bigl\{i<m:\ C_i\text{ is good for }t+a\,c_\sigma(z_i,i)/P_\sigma\bigr\}.$$
--
--   **Statement.** Under these assumptions, for every depth $h\ge0$ and every $t\in\mathbb T$ with $\varepsilon\le\|t\|$,
--
--   $$
--   \Pr_{C\in\mathcal C_h}\bigl[\,C\text{ is good for }t\,\bigr]\ \ge\ \frac{9}{10}.
--   $$
--
--   This is the probabilistic heart of the circle construction: for each fixed shift $t$ bounded away from $0$, most configurations are good for $t$, and goodness is exactly the hypothesis under which the separation theorem forces a large edit deficit between the word of a state and the word of the same state shifted by $t$.
--
--   **Formalization Note** $\mathbb T$ is `UnitAddCircle`, $u/n$ is `u • point n`, and $\|t\|$ is the norm on `UnitAddCircle`. Configurations are `Config I L (16 * k * s) h`, goodness is `Good ε r j h C t`, $P_\sigma$ is `period r j σ` and $c_\sigma$ is `coefficient r j σ` (with $\bar z$ = `z.val`). The primes are an injective `r : I → ℕ`, the quantity $U^k$ is computed in $\mathbb N$ before being cast to $\mathbb R$, and $16k/|I|$ is real division.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/CircleTree.lean#L435-L458

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

open OAI OAI.TreeEdit OAI.TreeEdit.TorusTree
open scoped BigOperators
open Classical
open FiniteProbability

theorem OAI.TreeEdit.TorusTree.good_probability {I : Type} [Fintype I] {k s L U : ℕ} [NeZero L]
    (r : I → ℕ) (hr : ∀ i, Nat.Prime (r i)) (hi : Function.Injective r)
    (hr10 : ∀ i, 10 ≤ r i) (hU : 1 ≤ U) (hrU : ∀ i, r i ≤ U)
    (hL : ∀ i, r i ∣ L) (j : Fin (16 * k) ↪ I)
    {ε : ℝ} (hgrid : ∀ i, 2 * ε * r i < 1)
    (hε : 2 * ε * ((U ^ k : ℕ) : ℝ) ^ 2 < 1)
    (herr : (16 * k : ℝ) / Fintype.card I + (U : ℝ) ^ (16 * k) * (4 / 5 : ℝ) ^ (k * s) ≤ 1 / 10)
    (h : ℕ) (t : UnitAddCircle) (ht : ε ≤ ‖t‖) :
    9 / 10 ≤ probability (fun C : Config I L (16 * k * s) h => Good ε r j h C t) := by sorry
