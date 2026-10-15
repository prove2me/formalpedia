-- Prove2me | Theorems.Thm_OAI_QAC_eventually_backward_cost
-- name    : OAI.QAC.eventually_backward_cost
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:47:46.677322+00:00
-- url     : https://prove2.me/theorems/1ab3cecb-f0bf-4f22-b480-91821d39807a
-- title:
--   Exponential error budget of the backward localization step
-- statement:
--   Let $s,a,u,w,t$ be real numbers with
--   $$0\le s<a<u<w<t .$$
--   Then for all sufficiently large natural numbers $N$,
--   $$
--   e^{N^u-N^w}+e^{-N^a}+\bigl(1+e^{N^u}\bigr)\,e^{-N^t}\le e^{-2N^s},
--   $$
--   where all powers of $N$ are real powers.
--
--   The three terms on the left are the contributions $A$, $E$ and $(1+B)T$ in the finite backward estimate $\|HQP\|^2\le A+E+(1+B)T$ with $A=e^{N^u}\cdot e^{-N^w}$ (a polynomial of weight at most $e^{N^u}$ times the transition bound $e^{-N^w}$ for product projections of small support), $B=e^{N^u}$, polynomial approximation error $E=e^{-N^a}$ and reverse transition $T=e^{-N^t}$. The lemma shows that the total is at most $e^{-2N^s}$, so the transition amplitude itself is at most $e^{-N^s}$.
--
--   **Formalization Note** "For all sufficiently large $N$" is the filter statement `∀ᶠ N : ℕ in atTop`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Asymptotics.lean#L260-L283

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

theorem OAI.QAC.eventually_backward_cost {s a u w t : ℝ} (hs : 0 ≤ s) (hsa : s < a)
    (hau : a < u) (huw : u < w) (hwt : w < t) :
    ∀ᶠ N : ℕ in atTop,
      Real.exp ((N:ℝ)^u-(N:ℝ)^w) + Real.exp (-((N:ℝ)^a)) +
        (1+Real.exp ((N:ℝ)^u))*Real.exp (-((N:ℝ)^t)) ≤ Real.exp (-2*(N:ℝ)^s) := by sorry
