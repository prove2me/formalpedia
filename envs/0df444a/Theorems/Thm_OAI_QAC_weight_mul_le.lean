-- Prove2me | Theorems.Thm_OAI_QAC_weight_mul_le
-- name    : OAI.QAC.weight_mul_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:40:07.197967+00:00
-- url     : https://prove2.me/theorems/7c85dae4-18cc-46c4-939b-46d178993a14
-- title:
--   Submultiplicativity of the weighted coefficient norm of real polynomials
-- statement:
--   For $R\in\mathbb R$ and a real polynomial $p=\sum_k c_kX^k$ define its weight
--   $$\|p\|_R=\sum_k|c_k|\,R^k .$$
--   If $R\ge0$, then for all $p,q\in\mathbb R[X]$
--   $$
--   \|pq\|_R\le\|p\|_R\,\|q\|_R .
--   $$
--
--   For $R\ge0$ the weight is the $\ell^1$ norm of the coefficient sequence with weights $R^k$, and the lemma says that it is submultiplicative. It bounds the weight of the Chebyshev-based approximating polynomials, which are built from products and compositions, and the weight in turn bounds $\|p(\mathcal N)\|$ for an operator $\mathcal N$ of norm at most $R$, term by term.
--
--   **Formalization Note** The weight is `weight R p`, defined with `Polynomial.sum` over the support of $p$ (with $R^0=1$); the hypothesis is `hR : 0 ≤ R`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Polynomial.lean#L54-L71

import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Count
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Spectral
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Transition
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Reflection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Polynomial

open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Filter Asymptotics

theorem OAI.QAC.weight_mul_le {R : ℝ} (hR : 0 ≤ R) (p q : ℝ[X]) :
    weight R (p * q) ≤ weight R p * weight R q := by sorry
