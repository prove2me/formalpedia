-- Prove2me | Theorems.Thm_HardyFiveAxioms_classical_no_continuous_pure_path
-- name    : HardyFiveAxioms.classical_no_continuous_pure_path
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T16:49:30.124429+00:00
-- url     : https://prove2.me/theorems/05e7549c-7eb7-4841-9c06-ec617f8bcae3
-- title:
--   Classical theory: no continuous path through pure states
-- statement:
--   Let $N\in\mathbb N$ and let $\gamma:[0,1]\to\mathbb R^N$ be a continuous path such that $\gamma(t)$ is a pure state of the classical state space $S^{\rm cl}_N$ for every $t$. Then $\gamma$ is constant:
--
--   $$\gamma(t)=\gamma(0)\qquad\text{for all }t\in[0,1].$$
--
--   Hence classical probability theory violates the continuity axiom: a continuous reversible transformation would move a pure state along a continuous path of pure states, which is impossible between two distinct basis states.
--
--   **Formalization Note** The path is a continuous map on `unitInterval` with the Euclidean (product) topology on $\mathbb R^N$.
-- source:
--   L. Hardy, *Quantum Theory From Five Reasonable Axioms*, arXiv:quant-ph/0101012v4 (2001), https://arxiv.org/abs/quant-ph/0101012, pp. 5–6, Section 4, final paragraph; p. 15, Section 7, paragraph on classical systems

import Mathlib
import Definitions.Def_hardy2001_states

namespace HardyFiveAxioms

/-- Hardy 2001, Sections 4 and 7: in classical probability theory there is no continuous
trajectory through the pure states connecting two different pure states: a continuous path
`[0,1] → ℝᴺ` that stays within the pure states is constant. -/
theorem classical_no_continuous_pure_path (N : ℕ) (γ : unitInterval → (Fin N → ℝ))
    (hγ : Continuous γ) (hpure : ∀ t, γ t ∈ pureStates (classicalStates N)) :
    ∀ t, γ t = γ 0 := by sorry

end HardyFiveAxioms
