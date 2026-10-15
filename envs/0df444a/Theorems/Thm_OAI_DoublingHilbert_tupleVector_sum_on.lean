-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_tupleVector_sum_on
-- name    : OAI.DoublingHilbert.tupleVector_sum_on
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:04:08.809764+00:00
-- url     : https://prove2.me/theorems/228a68ce-ad7a-473f-bff9-9fc5b0d8a4bb
-- title:
--   The displacement part of a strip point as a sum of level components over any finite superset of the support
-- statement:
--   Work in real $\ell^2$ with standard unit vectors $e_0,e_1,\dots$, scales $r_j=1000^{-(j+1)}$ and coordinate indices $c(j,i)=2+\pi(j,i)$, where $\pi$ is a pairing bijection of $\mathbb{N}\times\mathbb{N}$ onto $\mathbb{N}$. For a finitely supported tuple $w:\mathbb{N}\to\mathbb{N}$ with support $\operatorname{supp} w=\{j: w_j\neq0\}$, its displacement vector and its level-$j$ component are
--   $$
--   \tau(w)=\sum_{j\in\operatorname{supp} w} r_j\,e_{c(j,\,w_j-1)},\qquad \epsilon_j(w)=\begin{cases}0, & w_j=0,\\ r_j\,e_{c(j,\,w_j-1)}, & w_j\neq0.\end{cases}
--   $$
--
--   **Theorem.** Let $w$ be a finitely supported tuple and let $s\subseteq\mathbb{N}$ be a finite set with $\operatorname{supp} w\subseteq s$. Then
--   $$
--   \tau(w)=\sum_{j\in s}\epsilon_j(w).
--   $$
--
--   The identity lets the displacement parts of two points $z(p,w)=p_1e_0+p_2e_1+\tau(w)$ and $z(q,w')$ of the strip construction be written over a common finite index set, for instance $s=\operatorname{supp} w\cup\operatorname{supp} w'$, so that their difference splits level by level into the differences $\epsilon_j(w)-\epsilon_j(w')$.
--
--   **Formalization Note** Here $\tau(w)$ is `tupleVector w`, $\epsilon_j(w)$ is `entryVector w j`, the tuple has type `Tuple = ℕ →₀ ℕ`, and its support is the finset `w.support`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Construction.lean#L211-L225

import Mathlib
import Definitions.Def_CompactBanach
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction

open OAI OAI.DoublingHilbert
open scoped BigOperators
open Set

theorem OAI.DoublingHilbert.tupleVector_sum_on (w : Tuple) (s : Finset ℕ) (hs : w.support ⊆ s) :
    tupleVector w = ∑ j ∈ s, entryVector w j := by sorry
