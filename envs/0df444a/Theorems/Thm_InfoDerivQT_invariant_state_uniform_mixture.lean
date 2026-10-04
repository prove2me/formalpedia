-- Prove2me | Theorems.Thm_InfoDerivQT_invariant_state_uniform_mixture
-- name    : InfoDerivQT.invariant_state_uniform_mixture
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-02T14:24:42.770976+00:00
-- url     : https://prove2.me/theorems/56f11d18-5422-4083-a641-9b06cf32ed63
-- title:
--   Theorem 9 (with Lemma 10) — the invariant state is $\chi_A=\frac1{d_A}\sum_i\varphi_i$
-- statement:
--   Let $T$ satisfy the six principles, $A$ a system and $\{\varphi_i\}_{i=1}^N$ a maximal set of perfectly distinguishable pure states. Put $\chi=\frac1N\sum_{i=1}^N\varphi_i$. Then
--
--   1. $\mathcal U\chi=\chi$ for every reversible transformation $\mathcal U$ of $A$;
--   2. $\chi$ is the only normalized state of $A$ with this property.
--
--   Thus the unique invariant state $\chi_A$ of Lemma 10 equals $\frac1{d_A}\sum_i\varphi_i$ for every maximal set.
-- source:
--   G. Chiribella, G. M. D'Ariano, P. Perinotti, *Informational derivation of quantum theory*, Phys. Rev. A 84, 012311 (2011), https://doi.org/10.1103/PhysRevA.84.012311 (arXiv:1011.6451), p. 012311-17, Sec. VIII, Theorem 9; uniqueness of the invariant state: p. 012311-10, Lemma 10

import Mathlib
import Definitions.Def_InfoDerivQT_principles

namespace InfoDerivQT
theorem invariant_state_uniform_mixture (T : OPT) (hT : T.SatisfiesPrinciples) (A : T.Sys)
    {N : ℕ} (φ : Fin N → Vec (T.size A)) (hφ : T.IsMaximalPerfDistPure A φ) :
    (∀ U : Vec (T.size A) →ₗ[ℝ] Vec (T.size A), T.IsReversible A A U →
        U ((1 / (N : ℝ)) • ∑ i, φ i) = (1 / (N : ℝ)) • ∑ i, φ i) ∧
    ∀ ω ∈ T.St1 A, (∀ U : Vec (T.size A) →ₗ[ℝ] Vec (T.size A), T.IsReversible A A U →
        U ω = ω) → ω = (1 / (N : ℝ)) • ∑ i, φ i := by sorry
end InfoDerivQT
