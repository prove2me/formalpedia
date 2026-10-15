-- Prove2me | Theorems.Thm_OAI_QAC_list_disjoint_hits_length
-- name    : OAI.QAC.list_disjoint_hits_length
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:35:51.452696+00:00
-- url     : https://prove2.me/theorems/4a059c53-2af6-46c3-9c75-7b53e209c0da
-- title:
--   A list of pairwise disjoint sets that all meet $S$ has length at most $|S|$
-- statement:
--   Let $f$ assign to every element $a$ of a type $\iota$ a finite subset $f(a)$ of a type $\kappa$ (with decidable equality), and let $l=(a_1,\dots,a_n)$ be a list of elements of $\iota$ such that $f(a_j)\cap f(a_k)=\varnothing$ for all positions $j<k$. Let $S\subseteq\kappa$ be a finite set such that $f(a_j)\cap S\ne\varnothing$ for every entry $a_j$ of $l$. Then
--   $$
--   n\le |S| .
--   $$
--
--   This is a pigeonhole statement: different entries must meet $S$ in different points. In the circuit lower bound it shows that, in a parallel layer of gates with pairwise disjoint supports, the number of gates whose support meets the support of a product projection $P_A^0$ is at most $|\operatorname{supp}A|$; this keeps the cost of passing one layer bounded by $9^{|\operatorname{supp}A|}$.
--
--   **Formalization Note** Pairwise disjointness is `List.Pairwise` over positions, and $n$ is the list length, counted with multiplicity. A repeated entry $a$ would need $f(a)$ disjoint from itself, i.e. empty, which is incompatible with meeting $S$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Transition.lean#L91-L112

import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Count
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Spectral
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Transition

open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

theorem OAI.QAC.list_disjoint_hits_length {ι κ : Type*} [DecidableEq κ]
    (f : ι → Finset κ) (l : List ι) (hl : l.Pairwise (fun a b => Disjoint (f a) (f b)))
    (S : Finset κ) (hS : ∀ a ∈ l, (f a ∩ S).Nonempty) : l.length ≤ S.card := by sorry
