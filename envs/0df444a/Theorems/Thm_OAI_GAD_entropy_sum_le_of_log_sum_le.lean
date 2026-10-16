-- Prove2me | Theorems.Thm_OAI_GAD_entropy_sum_le_of_log_sum_le
-- name    : OAI.GAD.entropy_sum_le_of_log_sum_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:17:19.793781+00:00
-- url     : https://prove2.me/theorems/fe3b7c15-8737-4703-a89c-97bd07b4b608
-- title:
--   Signed entropy sums are controlled by signed logarithmic resolvent sums
-- statement:
--   Let $\iota$ be a finite index set, and let real numbers $c_i$ (of arbitrary sign) and $a_i\ge0$ be given for $i\in\iota$. Write $\eta(x)=-x\log x$ (natural logarithm, $\eta(0)=0$). Assume
--
--   1. the linear (trace) condition $\sum_{i\in\iota}c_ia_i=0$, and
--   2. the logarithmic condition $\sum_{i\in\iota}c_i\log\bigl(1+a_i/t\bigr)\le0$ for every real $t>0$.
--
--   Then
--
--   $$
--   \sum_{i\in\iota}c_i\,\eta(a_i)\le0.
--   $$
--
--   This is a scalar comparison principle: signed combinations of the entropy function $\eta$ are controlled by the same signed combinations of the logarithmic resolvent functions $a\mapsto\log(1+a/t)$, $t>0$. Applied to the eigenvalues of positive semidefinite matrices with weights $\pm1$, it converts inequalities between log-determinants $\log\det(I+rA)$ into inequalities between von Neumann entropies; applied to explicit finite spectra, it reduces entropy-deficit inequalities to elementary logarithmic ones.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/LogDetEntropy.lean#L66-L94

import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy

open OAI OAI.GAD
universe u_1 u_2 u_3 u_4 u_5
open scoped BigOperators
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set

theorem OAI.GAD.entropy_sum_le_of_log_sum_le {ι : Type u_1} [Fintype ι]
    (c a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (htrace : ∑ i, c i * a i = 0)
    (hlog : ∀ t : ℝ, 0 < t → ∑ i, c i * Real.log (1 + a i / t) ≤ 0) :
    ∑ i, c i * Real.negMulLog (a i) ≤ 0 := by sorry
