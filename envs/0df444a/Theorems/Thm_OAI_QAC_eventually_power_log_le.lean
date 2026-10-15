-- Prove2me | Theorems.Thm_OAI_QAC_eventually_power_log_le
-- name    : OAI.QAC.eventually_power_log_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:46:31.563715+00:00
-- url     : https://prove2.me/theorems/5a6908d8-21dd-4445-90ae-7e53ba32ba71
-- title:
--   A strict power gap absorbs a constant times a logarithm
-- statement:
--   Let $s<t$ be real numbers and let $C\in\mathbb R$. Then for all sufficiently large natural numbers $N$,
--   $$
--   C\,N^{s}\log N\le N^{t},
--   $$
--   where $N^s$ and $N^t$ are real powers and $\log$ is the natural logarithm.
--
--   This elementary asymptotic estimate is used repeatedly in the localization argument to check that losses of the form $N^{s}\log N$ in an exponent, coming for instance from counting mismatch patterns or from the weight $(1+N)^{r}$ of a polynomial with $r\approx N^s$, are dominated by any strictly larger power $N^t$.
--
--   **Formalization Note** "For all sufficiently large $N$" is the filter statement `∀ᶠ N : ℕ in atTop`, i.e. there is $N_0$ such that the inequality holds for every natural number $N\ge N_0$. The constant $C$ is an arbitrary real number.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Asymptotics.lean#L23-L40

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

theorem OAI.QAC.eventually_power_log_le {s t : ℝ} (hst : s < t) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ s * Real.log N ≤ (N : ℝ) ^ t := by sorry
