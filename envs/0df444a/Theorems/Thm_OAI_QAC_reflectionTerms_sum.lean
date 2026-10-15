-- Prove2me | Theorems.Thm_OAI_QAC_reflectionTerms_sum
-- name    : OAI.QAC.reflectionTerms_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:38:59.509975+00:00
-- url     : https://prove2.me/theorems/d0483de5-023e-4a30-83dd-fa6bf9507e36
-- title:
--   Expansion of a product of reflections with disjoint supports into product projections
-- statement:
--   For a count $A$ on $N$ qubits (a support $S_A$ with unit vectors $v_i\in\mathbb C^2$, $i\in S_A$) let $P_A^0$ be its zero-mismatch product projection and $R_A=I-2P_A^0$ the corresponding reflection. For counts $A,C$ let $A\vee C$ be their join (support $S_A\cup S_C$, with the axes of $A$ on $S_A$ and those of $C$ elsewhere), and let $\varnothing$ be the empty count, so $P^0_\varnothing=I$. For a list $l$ of counts define the list $\mathcal T(l)$ of pairs (real coefficient, count) recursively by
--   $$\mathcal T(\,)=\bigl((1,\varnothing)\bigr),\qquad\mathcal T(A,l)=\mathcal T(l)\mathbin{+\!\!+}\bigl((-2c,\,A\vee C)\bigr)_{(c,C)\in\mathcal T(l)} .$$
--
--   If $l=(A_1,\dots,A_m)$ is a list of counts with pairwise disjoint supports, then
--   $$
--   \sum_{(c,C)\in\mathcal T(l)}c\,P_C^0=R_{A_1}R_{A_2}\cdots R_{A_m}.
--   $$
--   Unwinding the recursion, $\mathcal T(l)$ has one entry for each $J\subseteq\{1,\dots,m\}$, with coefficient $(-2)^{|J|}$ and the join of the $A_j$ with $j\in J$; so the product of reflections is a signed combination of $2^m$ zero-mismatch projections of single counts.
--
--   This identity turns a parallel layer of reflections about product projections (for example Toffoli gates) into a linear combination of product projections whose coefficients have total absolute value $3^m$, so that transition bounds for single product projections can be summed over the layer.
--
--   **Formalization Note** The left side is a list sum over `reflectionTerms l` (multiplicities are kept), the coefficients act as real scalars on complex matrices, and the right side is `reflectList l`, the ordered product of `reflect A = 1 - (2:ℝ) • A.zero`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Reflection.lean#L84-L101

import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Count
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Spectral
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Transition
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Reflection

open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

theorem OAI.QAC.reflectionTerms_sum {N : ℕ} (l : List (Count N))
    (hl : l.Pairwise (fun A B => Disjoint A.support B.support)) :
    ((reflectionTerms l).map (fun p => p.1 • p.2.zero)).sum = reflectList l := by sorry
