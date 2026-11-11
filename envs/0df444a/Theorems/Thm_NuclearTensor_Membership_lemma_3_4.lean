-- Prove2me | Theorems.Thm_NuclearTensor_Membership_lemma_3_4
-- name    : NuclearTensor.Membership.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:18:24.790326+00:00
-- url     : https://prove2.me/theorems/246080c2-3477-42af-ac0b-abee3dec8830
-- title:
--   Lemma 3.4 — discarded-message energy
-- statement:
--   Use the maps actually constructed by Algorithm 1 and local vectors $x_j\in H_j$ with $\|x_j\|\le1$. Define $p_0=1$, $p_j=U_j^\dagger(p_{j-1}\otimes x_j)$ and $q_j=(I-U_jU_j^\dagger)(p_{j-1}\otimes x_j)$. Then
--   $$\sum_{j=1}^{k-1}\|q_j\|^2\le1.$$
--   The source context supplying these maps, including the input norm bound, is explicit. No energy estimate is assumed. For $k=1$ the sum is empty and equals zero. This is the quantitative energy target for the uniform product-test result.
--
--   Differences from the source:
--
--   - encoding: finite-dimensional real Hilbert spaces, indexed from 1 → zero-based row-major Euclidean coordinates, allowing zero-dimensional local spaces; reason: orthonormal coordinates represent every source finite real Hilbert space; positive tensor order is the source convention
-- source:
--   Martino Bernasconi, Giulio Malavolta, STOC 2027 submission #945 (October 2026), p.13, Lemma 3.4

import Definitions.Def_NuclearTensor_Membership_Optimization

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal

namespace NuclearTensor.Membership

theorem lemma_3_4 (σ : Spectral) (ds : List ℕ) (hk : ds ≠ [])
    (M : Tensor ds) (hM : ‖M‖ ≤ 1) (η : ℝ) (hη : 0 < η)
    (C : PrefixData ds) (hC : algorithm1 σ η M C)
    (x : Tuple ds) (hx : ∀ j < ds.length, ‖x j‖ ≤ 1) :
    (∑ j : Fin (ds.length - 1), ‖discardedMessage C x j.val‖ ^ 2) ≤ 1 := by sorry

end NuclearTensor.Membership
