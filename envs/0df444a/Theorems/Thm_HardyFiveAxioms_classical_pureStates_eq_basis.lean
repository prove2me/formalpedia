-- Prove2me | Theorems.Thm_HardyFiveAxioms_classical_pureStates_eq_basis
-- name    : HardyFiveAxioms.classical_pureStates_eq_basis
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T16:01:45.055262+00:00
-- url     : https://prove2.me/theorems/04334560-0a52-449c-b9a3-f4e6f21b0b72
-- title:
--   Classical pure states are exactly the $N$ basis states
-- statement:
--   For every dimension $N$, the pure states of the classical state space $S^{\rm cl}_N=\{p\in\mathbb R^N: p\ge0,\ \sum_np_n\le1\}$ are exactly the $N$ basis states:
--
--   $$S^{\rm cl}_{N,\rm pure}=\{e_1,\dots,e_N\}.$$
--
--   This is the description of classical probability theory in Section 4 (Eq. (2)): the extremal states are the basis states and the null state, and the pure states are the basis states. In particular there are only finitely many pure states.
--
--   **Formalization Note** Pure states, basis states and $S^{\rm cl}_N$ are as in `hardy2001_states`.
-- source:
--   L. Hardy, *Quantum Theory From Five Reasonable Axioms*, arXiv:quant-ph/0101012v4 (2001), https://arxiv.org/abs/quant-ph/0101012, pp. 4–5, Section 4, Eqs. (1)–(3) and the definition of pure states

import Mathlib
import Definitions.Def_hardy2001_states

namespace HardyFiveAxioms

/-- Hardy 2001, Section 4, Eq. (2): the pure states of classical probability theory in
dimension `N` are exactly the `N` basis states. -/
theorem classical_pureStates_eq_basis (N : ℕ) :
    pureStates (classicalStates N) = Set.range (basisState (N := N)) := by sorry

end HardyFiveAxioms
