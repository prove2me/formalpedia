-- Prove2me | Theorems.Thm_OAI_QAC_finite_scale_induction
-- name    : OAI.QAC.finite_scale_induction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:49:07.678989+00:00
-- url     : https://prove2.me/theorems/b317b1ac-c363-49c5-8914-f0b25af746e8
-- title:
--   Finite bootstrap over pairs of scale exponents
-- statement:
--   Let $\mathcal B(s,t)$ be an arbitrary relation between real numbers $s$ and $t$. Assume:
--
--   1. (large scales) $\mathcal B(s,t)$ holds whenever $0\le s<t$ and $t>1$;
--   2. (backward step) for all real $s,t,a,b,u,w$ with
--   $$0\le s<a<u<w<t<b\qquad\text{and}\qquad\frac{a+b}2<u,$$
--   $\mathcal B(t,b)$ implies $\mathcal B(s,t)$.
--
--   Then
--   $$
--   \mathcal B(s,t)\quad\text{for all real } s,t \text{ with } 0\le s<t .
--   $$
--
--   The backward step trades a pair $(s,t)$ for a pair $(t,b)$ further up, and the theorem says that finitely many such trades always reach the regime $t>1$, so that the relation holds for all admissible pairs. In the localization theorem it is applied, at each circuit depth, to the relation that the uniform localization bound $e^{-N^s}$ holds at mismatch threshold $N^t$; the case $t>1$ is trivial because for large $N$ the threshold $N^t$ exceeds the number $N$ of qubits, and the backward step is the polynomial-approximation argument.
--
--   **Formalization Note** $\mathcal B$ is an arbitrary `ℝ → ℝ → Prop`; the statement is pure real arithmetic and involves no operator-theoretic assumption.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/ScaleInduction.lean#L11-L113

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
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Polynomial Filter Asymptotics

theorem OAI.QAC.finite_scale_induction (B : ℝ → ℝ → Prop)
    (large : ∀ s t, 0 ≤ s → s < t → 1 < t → B s t)
    (backstep : ∀ s t a b u w, 0 ≤ s → s < a → a < u → u < w → w < t → t < b →
      (a + b) / 2 < u → B t b → B s t) :
    ∀ s t, 0 ≤ s → s < t → B s t := by sorry
