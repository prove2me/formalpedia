-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_Ancestry_pooled_tail_test
-- name    : OAI.DiamondDistortion.Ancestry.pooled_tail_test
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:56:20.060352+00:00
-- url     : https://prove2.me/theorems/9d4b90b5-309d-4b30-9133-65bba8f41233
-- title:
--   Pooled tail bound for the signed mean of a finite law of disjoint-segment atoms
-- statement:
--   Let $V$ be a set carrying an *ancestry*: a partial order $\le$ (read $a\le b$ as "$a$ is an ancestor of $b$") in which the ancestors of every vertex form a chain, i.e. $a\le c$ and $b\le c$ imply $a\le b$ or $b\le a$. A *segment* is a finite set of the form $[a,b]=\{v\in V:\ a\le v\le b\}$ with $a\le b$, and a *segment family* $\mathcal F=(S_1,\dots,S_n)$ is a finite list of pairwise disjoint segments. For a finitely supported $p:V\to\mathbb{R}$ and a finite $S\subseteq V$ write $p(S)=\sum_{v\in S}p(v)$, and let $\|p\|_{\mathrm{seg}}=\sup_{\mathcal F}\big(\sum_{i}p(S_i)^2\big)^{1/2}$ be the *segment norm*, the supremum over all segment families.
--
--   Let $J$ be the completion of the space of finitely supported functions $V\to\mathbb{R}$ under $\|\cdot\|_{\mathrm{seg}}$; write $\hat p\in J$ for the image of $p$ and $e_v\in J$ for the image of the indicator of $\{v\}$. Let $J^*$ be the space of all continuous linear functionals on $J$, with the operator norm $\|x\|=\sup_{\|u\|\le1}|x(u)|$, and let $e_v^*\in J^*$ be the coordinate functional, i.e. the continuous extension of $p\mapsto p(v)$. For a finite $H\subseteq V$ the head and tail projections on $J^*$ are $P_Hx=\sum_{v\in H}x(e_v)\,e_v^*$ and $Q_Hx=x-P_Hx$. For a finite $S\subseteq V$ let $\sigma_S=\sum_{v\in S}e_v^*$. A set $H\subseteq V$ is *ancestral* if $a\le b$ and $b\in H$ imply $a\in H$.
--
--   An *atom of radius $R$* consists of a segment family $(S_1,\dots,S_n)$ and coefficients $a_1,\dots,a_n\in\mathbb{R}$ with $\sum_ia_i^2\le R^2$; its value is the functional $\mathrm{val}(A)=\sum_ia_i\sigma_{S_i}\in J^*$. A *bipolar law* of radius $R$ for $x,y\in J^*$, indexed by a finite set $\Omega$, consists of atoms $A_\omega$ of radius $R$, weights $w_\omega\ge0$ with $\sum_\omega w_\omega=1$, and signs $\varepsilon_\omega$ with $|\varepsilon_\omega|=1$, such that
--
--   $$
--   \sum_{\omega\in\Omega}w_\omega\,\mathrm{val}(A_\omega)=x,\qquad\sum_{\omega\in\Omega}w_\omega\,\varepsilon_\omega\,\mathrm{val}(A_\omega)=y .
--   $$
--
--   Let $H,K\subseteq V$ be finite ancestral sets, let $R\in\mathbb{R}$ and $x,y\in J^*$, and let a bipolar law of radius $R$ for $x,y$ be given in which every segment of every atom is contained in $K$. Assume that $x(e_v)=0$ for all $v\notin H$. Let $p$ be finitely supported with $p(v)=0$ for all $v\notin H$ and $\|p\|_{\mathrm{seg}}\le1$. Then
--
--   $$
--   \|Q_Hy\|\le2\sqrt{R^2-x(\hat p)^2} .
--   $$
--
--   The law represents $x$ as an average of atoms and $y$ as a signed average of the same atoms. The bound says that the part of $y$ beyond the head $H$ is small when a test vector $p$ supported in $H$ nearly norms $x$ at scale $R$: the more of the budget $R^2$ is used by $x(\hat p)^2$, the less is left for the tail of $y$. This is the finite, fully explicit core of the lens estimates for the dual of the segment-norm space; no convexity modulus of the space is assumed.
--
--   **Formalization Note** The vertex set is a type with an `Ancestry` instance, $H,K$ are `Finset`s, the law is `A.segments.BipolarLaw Ω R x y` (atoms carry their family and coefficients as data, and $\mathrm{val}$ is `Atom.value`), $\hat p$ is `A.segments.finiteEmbedding p`, and $Q_H$ is `A.segments.tailDual H`. The square root is `Real.sqrt`, which is $0$ on negative numbers. Under the hypotheses the radicand is in fact nonnegative.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/Ancestry.lean#L947-L1069

import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry

open OAI OAI.DiamondDistortion OAI.DiamondDistortion.Ancestry
universe u v
open scoped BigOperators Classical Topology
open Set
open scoped Classical
attribute [local instance] OAI.DiamondDistortion.Ancestry.instPartialOrder
variable {ι : Type*} [A : Ancestry ι]

theorem OAI.DiamondDistortion.Ancestry.pooled_tail_test {Ω : Type*} [Fintype Ω] {H K : Finset ι}
    (hH : A.Ancestral (H : Set ι)) (hK : A.Ancestral (K : Set ι))
    {R : ℝ} {x y : A.segments.Dual} (law : A.segments.BipolarLaw Ω R x y)
    (hFK : ∀ ω i,(law.atom ω).family.seg i ⊆ K)
    (hx : ∀ v,v ∉ H → x (A.segments.unitVector v)=0)
    (p : ι →₀ ℝ) (hp : ∀ v,v ∉ H → p v=0) (hpn : A.segments.primalSeminorm p ≤ 1) :
    ‖A.segments.tailDual H y‖ ≤
      2*Real.sqrt (R^2 - (x (A.segments.finiteEmbedding p))^2) := by sorry
