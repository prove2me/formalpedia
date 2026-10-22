-- Prove2me | Theorems.Thm_MultipartiteREE_Approx_lemma_3
-- name    : MultipartiteREE.Approx.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:25.56512+00:00
-- url     : https://prove2.me/theorems/faf33499-af36-4eb1-82f3-2476a790a4aa
-- title:
--   Lemma 3, p. 25 — separable comparison state for a pure state
-- statement:
--   For every pure state $\omega$ of an $n$-partite system, there is a countably decomposable separable state $\sigma$ with the same marginal on every party such that
--
--   $$H(\omega\|\sigma)\le\sum_{s=1}^{n-1}H(\omega_{A_s}).$$
--
--   This supplies the comparison state behind the marginal upper bound for relative entropy of entanglement. The formalization indexes the paper's parties by $\operatorname{Fin}(n+1)$, so the displayed sum is over all but the final party.
-- source:
--   Shirokov, Approximation of multipartite quantum states and the relative entropy of entanglement, arXiv:2103.12111v2, p. 25, Lemma 3

import Mathlib
import Definitions.Def_MultipartiteREE_Approx_Setting

noncomputable section

open Filter Topology
open scoped ENNReal
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State rankOne)
open QAlgorithms.Papers.Independent.Frontier18.P01 (homogeneousEntropy generalizedRelativeEntropy)

namespace MultipartiteREE.Approx

theorem lemma_3 {n : ℕ} {I : Fin (n + 1) → Type} [∀ s, Countable (I s)]
    (omega : State (Joint I))
    (hpure : ∃ u : Hilbert (Joint I), ‖u‖ = 1 ∧ omega.coefficients = rankOne u) :
    ∃ sigma : State (Joint I), sigma ∈ separableStates I ∧
      IsCountablyDecomposableN sigma.coefficients ∧
      (∀ s, marginal sigma.coefficients s = marginal omega.coefficients s) ∧
      generalizedRelativeEntropy omega.coefficients sigma.coefficients ≤
        ∑ s ∈ Finset.univ.erase (Fin.last n), marginalEntropy omega s := by sorry

end MultipartiteREE.Approx
