-- Prove2me | Theorems.Thm_InfoDerivQT_spectral_decomposition
-- name    : InfoDerivQT.spectral_decomposition
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-02T14:46:03.947639+00:00
-- url     : https://prove2.me/theorems/fbf1e343-f158-4b22-89ae-623a707a01ba
-- title:
--   Theorem 10 — spectral decomposition into perfectly distinguishable pure states
-- statement:
--   Let $T$ satisfy the six principles and $A$ a system. Every normalized state $\rho\in\mathrm{St}_1(A)$ can be written as
--
--   $$\rho=\sum_{i=1}^N p_i\,\varphi_i,\qquad p_i\ge0,\quad \sum_i p_i=1,$$
--
--   where $\varphi_1,\dots,\varphi_N$ are perfectly distinguishable pure states.
--
--   This is the operational counterpart of the spectral theorem for density matrices.
--
--   **Formalization Note** The paper states the result for mixed states; for pure states it holds trivially with $N=1$, so the formal statement covers all normalized states.
-- source:
--   G. Chiribella, G. M. D'Ariano, P. Perinotti, *Informational derivation of quantum theory*, Phys. Rev. A 84, 012311 (2011), https://doi.org/10.1103/PhysRevA.84.012311 (arXiv:1011.6451), p. 012311-17, Sec. VIII, Theorem 10 (Spectral decomposition)

import Mathlib
import Definitions.Def_InfoDerivQT_principles

namespace InfoDerivQT
theorem spectral_decomposition (T : OPT) (hT : T.SatisfiesPrinciples) (A : T.Sys)
    (ρ : Vec (T.size A)) (hρ : ρ ∈ T.St1 A) :
    ∃ (N : ℕ) (φ : Fin N → Vec (T.size A)) (p : Fin N → ℝ),
      T.PerfectlyDistinguishable A φ ∧ (∀ i, T.IsPure A (φ i)) ∧
      (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧ ρ = ∑ i, p i • φ i := by sorry
end InfoDerivQT
