-- Prove2me | Theorems.Thm_OAI_ParityWL_baseType_inl_iff
-- name    : OAI.ParityWL.baseType_inl_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:38:46.914863+00:00
-- url     : https://prove2.me/theorems/d81c1870-fb4c-4bb0-b31c-78d66f67ffc5
-- title:
--   Base vertices of main type $i$ are exactly the pairs $(i,d)$ with $d\in D_i$
-- statement:
--   Fix $t\in\mathbb{N}$ and a choice system $C$ on $t$: a finite domain $D_i$ for each $i\in[t]=\{0,\dots,t-1\}$, a finite label set $L_{ij}$ for each pair $i<j$, and label maps $\ell_{ij}\colon D_i\to L_{ij}$, $r_{ij}\colon D_j\to L_{ij}$. The template graph $T_t$ has the main vertices $i\in[t]$ and the helper vertices $h=(i,j;m)$ with $i<j$ and $m\in[t]\setminus\{i,j\}$. The base graph of $C$ has vertex set
--   $$
--   V_C=\{(i,d): i\in[t],\ d\in D_i\}\ \sqcup\ \{(h,q): h=(i,j;m)\text{ a helper},\ q\in L_{ij}\},
--   $$
--   and its type map $\pi\colon V_C\to[t]\sqcup\mathcal{H}_t$ sends $(i,d)\mapsto i$ and $(h,q)\mapsto h$, where $\mathcal{H}_t$ denotes the set of helpers.
--
--   **Theorem.** For every base vertex $v\in V_C$ and every main index $i\in[t]$,
--   $$
--   \pi(v)=i\iff v=(i,d)\ \text{ for some } d\in D_i.
--   $$
--
--   This inverts the type map on main vertices: a base vertex known only to project to the main template vertex $i$ carries an actual element of the domain $D_i$. It is used to read off a candidate choice $(d_i)_{i\in[t]}$ from vertices of the main types and to compare labels across edges of the base graph.
--
--   **Formalization Note** `BaseVertex C` is the sum type of the dependent pairs `(i, d)` with `d : C.Domain i` and the pairs `(h, q)` with `q : C.Label h.1.1`; `baseType` is the type map $\pi$, and `.inl i` denotes the main template vertex $i$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/BaseLabels.lean#L15-L27

import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BaseLabels

open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical
variable {t : ℕ} (C : ChoiceSystem t)

theorem OAI.ParityWL.baseType_inl_iff (v : BaseVertex C) (i : Fin t) :
    baseType v = .inl i ↔ ∃ d : C.Domain i, v = .inl ⟨i, d⟩ := by sorry
