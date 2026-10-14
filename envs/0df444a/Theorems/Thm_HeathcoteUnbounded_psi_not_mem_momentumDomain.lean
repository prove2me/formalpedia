-- Prove2me | Theorems.Thm_HeathcoteUnbounded_psi_not_mem_momentumDomain
-- name    : HeathcoteUnbounded.psi_not_mem_momentumDomain
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T14:36:04.521864+00:00
-- url     : https://prove2.me/theorems/e1f3fb4f-fd17-4a5c-b745-f6fc1907fe32
-- title:
--   $\psi$ has no absolutely continuous representative: $\psi\notin D(P)$
-- statement:
--   For the wave function $\psi$ of eq. (4) there is no function $g:\mathbb R\to\mathbb C$ that agrees with $\psi$ almost everywhere and is absolutely continuous on every compact interval $[a,b]$.
--
--   In the source's words, $\psi$ "is discontinuous at $x=1$ and so is not in the domain of $P$"; this shows the failure of $\psi\in D(Q)$ is independent of the canonical commutation relations.
--
--   **Formalization Note** Since elements of $L^2$ are a.e.-classes, the statement quantifies over all a.e.-representatives.
-- source:
--   A. Heathcote, "Unbounded Operators and the Incompleteness of Quantum Mechanics", Philosophy of Science 57 (1990), 523–534, pp. 5–6

import Mathlib
import Definitions.Def_HeathcoteUnbounded_Psi

open MeasureTheory

namespace HeathcoteUnbounded

theorem psi_not_mem_momentumDomain :
    ¬ ∃ g : ℝ → ℂ, psi =ᵐ[volume] g ∧ ∀ a b : ℝ, AbsolutelyContinuousOnInterval g a b := by sorry

end HeathcoteUnbounded
