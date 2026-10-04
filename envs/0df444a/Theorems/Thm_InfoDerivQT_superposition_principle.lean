-- Prove2me | Theorems.Thm_InfoDerivQT_superposition_principle
-- name    : InfoDerivQT.superposition_principle
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-02T16:49:22.890614+00:00
-- url     : https://prove2.me/theorems/bb903c70-1c3d-49de-904a-d1565ca8c2eb
-- title:
--   Theorem 16 — superposition principle: every probability vector is realized by a pure state
-- statement:
--   Let $T$ satisfy the six principles, $A$ a system, $\{\varphi_i\}_{i=1}^N$ a maximal set of perfectly distinguishable pure states, and $\{a_i\}_{i=1}^N$ an observation test with $(a_i|\varphi_j)=\delta_{ij}$. Then for every probability vector $(p_1,\dots,p_N)$, $p_i\ge0$, $\sum_ip_i=1$, there is a pure state $\varphi_p\in\mathrm{St}_1(A)$ with
--
--   $$(a_i|\varphi_p)=p_i\qquad(i=1,\dots,N).$$
-- source:
--   G. Chiribella, G. M. D'Ariano, P. Perinotti, *Informational derivation of quantum theory*, Phys. Rev. A 84, 012311 (2011), https://doi.org/10.1103/PhysRevA.84.012311 (arXiv:1011.6451), p. 012311-29, Sec. XII, Theorem 16 (Superposition principle for general systems)

import Mathlib
import Definitions.Def_InfoDerivQT_principles

namespace InfoDerivQT
theorem superposition_principle (T : OPT) (hT : T.SatisfiesPrinciples) (A : T.Sys)
    {N : ℕ} (φ : Fin N → Vec (T.size A)) (hφ : T.IsMaximalPerfDistPure A φ)
    (a : Fin N → Module.Dual ℝ (Vec (T.size A))) (ha : a ∈ T.ObsTest A (Fin N))
    (haφ : ∀ i j, a i (φ j) = if i = j then 1 else 0)
    (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    ∃ ψ ∈ T.St1 A, T.IsPure A ψ ∧ ∀ i, a i ψ = p i := by sorry
end InfoDerivQT
