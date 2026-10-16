-- Prove2me | Theorems.Thm_OAI_TreeEdit_TorusTree_fixed_residue_failure
-- name    : OAI.TreeEdit.TorusTree.fixed_residue_failure
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:51:26.665508+00:00
-- url     : https://prove2.me/theorems/99830729-bc20-488f-adb8-168a57320f7d
-- title:
--   For a fixed residue, fewer than $1/64$ of the children are good with probability at most $(4/5)^{ks}$
-- statement:
--   This statement concerns the random configurations used to build tree-structured words from points of the circle $\mathbb T=\mathbb R/\mathbb Z$. For $t\in\mathbb T$ let $\|t\|$ be the distance from $t$ to $0$ in $\mathbb T$ (the distance of a representative to the nearest integer), and for $u\in\mathbb N$ and $n\ge1$ write $u/n$ also for its image in $\mathbb T$. All probabilities are for the uniform distribution on the indicated finite set.
--
--   **Data.** Let $I$ be a finite set, $(r_v)_{v\in I}$ a family of primes with $r_v\ge10$, and $L\ge1$ an integer divisible by every $r_v$. Let $k,s,h$ be natural numbers, put $g=16k$ and $m=gs=16ks$, and let $j\colon\{0,\dots,g-1\}\to I$ be injective. Let $\varepsilon$ be a real number with $2\varepsilon r_v<1$ for all $v\in I$.
--
--   **Coefficients.** For a permutation $\sigma$ of $I$ let $P_\sigma=\prod_{u=0}^{g-1}r_{\sigma(j(u))}$. The $m$ children $i\in\{0,\dots,m-1\}$ are divided into $g$ groups of $s$ children, child $i$ lying in group $\gamma(i)=\lfloor i/s\rfloor$, and child $i$ carries the prime $p_{\sigma,i}=r_{\sigma(j(\gamma(i)))}$. For $z\in\mathbb Z/L\mathbb Z$ with representative $\bar z\in\{0,\dots,L-1\}$ put
--   $$c_\sigma(z,i)=1+(\bar z\bmod p_{\sigma,i})\cdot\frac{P_\sigma}{p_{\sigma,i}}.$$
--
--   **Configurations and goodness.** Let $\mathcal C_0=\{\ast\}$ and $\mathcal C_{h+1}=\mathrm{Sym}(I)\times(\mathbb Z/L\mathbb Z\times\mathcal C_h)^m$: a configuration of depth $h+1$ is a permutation $\sigma$ together with a residue $z_i$ and a configuration $C_i$ of depth $h$ for each child $i<m$. Goodness is defined by recursion on the depth: the configuration of depth $0$ is good for $t$ iff $\varepsilon\le\|t\|$, and $(\sigma,(z_i,C_i)_{i<m})$ is good for $t$ iff for every $a\in\{0,\dots,P_\sigma-1\}$
--   $$m\le 64\cdot\#\bigl\{i<m:\ C_i\text{ is good for } t+a\,c_\sigma(z_i,i)/P_\sigma\bigr\}.$$
--
--   **Statement.** Fix a permutation $\sigma$ of $I$ and a point $t\in\mathbb T$, and assume:
--   1. for every $t'\in\mathbb T$ with $\varepsilon\le\|t'\|$, a uniformly random $C\in\mathcal C_h$ is good for $t'$ with probability at least $9/10$;
--   2. for every $a\in\mathbb N$ with $\#\{u<g:\ r_{\sigma(j(u))}\nmid a\}\le k$ one has $\varepsilon\le\|t+a/P_\sigma\|$.
--
--   Then for every residue $a\in\{0,\dots,P_\sigma-1\}$, if $(z_i,C_i)_{i<m}$ is drawn uniformly from $(\mathbb Z/L\mathbb Z\times\mathcal C_h)^m$,
--
--   $$
--   \Pr\Bigl[\ 64\cdot\#\bigl\{i<m:\ C_i\text{ is good for } t+a\,c_\sigma(z_i,i)/P_\sigma\bigr\}<m\ \Bigr]\le\Bigl(\frac45\Bigr)^{ks}.
--   $$
--
--   So for one fixed residue $a$, the chance that fewer than a $1/64$ fraction of the children are good at the corresponding shifted points is exponentially small in $ks$. A union bound over the $P_\sigma$ residues then controls the probability that a configuration of depth $h+1$ with first component $\sigma$ fails to be good for $t$; this is the inductive step in showing that random configurations are good with probability at least $9/10$.
--
--   **Formalization Note** $\mathbb T$ is `UnitAddCircle`, $u/n$ is `u • point n` with `point n` the image of $1/n$, and $\|t\|$ is the norm on `UnitAddCircle`. Configurations are `Config I L (16 * k * s) h`, goodness is `Good ε r j h C t`, $P_\sigma$ is `period r j σ`, $c_\sigma(z,i)$ is `coefficient r j σ z i` (with $\bar z$ = `z.val`), and $\gamma$ is `group`, the first coordinate under $\{0,\dots,gs-1\}\cong\{0,\dots,g-1\}\times\{0,\dots,s-1\}$. `probability` is the uniform average of an indicator; the event is written as the negation of $16ks\le 64\cdot\#\{\dots\}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/CircleTree.lean#L329-L401

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

theorem OAI.TreeEdit.TorusTree.fixed_residue_failure {I : Type} [Fintype I] {k s L h : ℕ} [NeZero L]
    (r : I → ℕ) (hr : ∀ i, Nat.Prime (r i)) (hr10 : ∀ i, 10 ≤ r i)
    (hL : ∀ i, r i ∣ L) (j : Fin (16 * k) ↪ I)
    {ε : ℝ} (hgrid : ∀ i, 2 * ε * r i < 1)
    (ih : ∀ t : UnitAddCircle, ε ≤ ‖t‖ → 9 / 10 ≤
      probability (fun C : Config I L (16 * k * s) h => Good ε r j h C t))
    (σ : Equiv.Perm I) (t : UnitAddCircle)
    (hlist : ∀ a : ℕ, (Finset.univ.filter (fun v : Fin (16 * k) => ¬ r (σ (j v)) ∣ a)).card ≤ k →
      ε ≤ ‖t + a • point (period r j σ)‖) (a : Fin (period r j σ)) :
    probability (fun C : Fin (16 * k * s) → ZMod L × Config I L (16 * k * s) h =>
      ¬ 16 * k * s ≤ 64 * (Finset.univ.filter (fun i =>
        Good ε r j h (C i).2 (t + (a.val * coefficient r j σ (C i).1 i) • point (period r j σ)))).card) ≤
      (4 / 5 : ℝ) ^ (k * s) := by sorry
