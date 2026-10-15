-- Prove2me | Theorems.Thm_OAI_ParityWL_baseType_inr_iff
-- name    : OAI.ParityWL.baseType_inr_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:39:44.239716+00:00
-- url     : https://prove2.me/theorems/f092b17f-efb6-46eb-ac03-dc2c6eb2cc4f
-- title:
--   Base vertices of helper type $h$ are exactly the pairs $(h,q)$ with $q$ a label of its pair
-- statement:
--   Fix $t\in\mathbb{N}$ and a choice system $C$ on $t$: a finite domain $D_i$ for each $i\in[t]=\{0,\dots,t-1\}$, a finite label set $L_{ij}$ for each pair $i<j$, and label maps $\ell_{ij}\colon D_i\to L_{ij}$, $r_{ij}\colon D_j\to L_{ij}$. The template graph $T_t$ has the main vertices $i\in[t]$ and the helper vertices $h=(i,j;m)$ with $i<j$ and $m\in[t]\setminus\{i,j\}$. The base graph of $C$ has vertex set
--   $$
--   V_C=\{(i,d): i\in[t],\ d\in D_i\}\ \sqcup\ \{(h,q): h=(i,j;m)\text{ a helper},\ q\in L_{ij}\},
--   $$
--   and its type map $\pi\colon V_C\to[t]\sqcup\mathcal{H}_t$ sends $(i,d)\mapsto i$ and $(h,q)\mapsto h$, where $\mathcal{H}_t$ denotes the set of helpers.
--
--   **Theorem.** For every base vertex $v\in V_C$ and every helper $h=(i,j;m)\in\mathcal{H}_t$,
--   $$
--   \pi(v)=h\iff v=(h,q)\ \text{ for some } q\in L_{ij}.
--   $$
--
--   This inverts the type map on helper vertices: a base vertex known only to project to the helper $h$ carries a label of the pair $(i,j)$ underlying $h$. Together with the analogous statement for main vertices it is used to identify the endpoints of base edges by their types, for instance to compare the label of a helper base vertex with the left or right label of an adjacent main base vertex.
--
--   **Formalization Note** `BaseVertex C` is the sum type of the pairs `(i, d)` with `d : C.Domain i` and the pairs `(h, q)` with `q : C.Label h.1.1` (here `h.1.1` is the pair $(i,j)$ of the helper); `baseType` is the type map $\pi$, and `.inr h` denotes the helper template vertex $h$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/BaseLabels.lean#L29-L41

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

theorem OAI.ParityWL.baseType_inr_iff (v : BaseVertex C) (h : Helper t) :
    baseType v = .inr h ↔ ∃ q : C.Label h.1.1, v = .inr ⟨h, q⟩ := by sorry
