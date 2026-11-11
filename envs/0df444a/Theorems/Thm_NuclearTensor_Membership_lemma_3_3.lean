-- Prove2me | Theorems.Thm_NuclearTensor_Membership_lemma_3_3
-- name    : NuclearTensor.Membership.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:18:25.131217+00:00
-- url     : https://prove2.me/theorems/2330e177-d40f-4807-93e2-3bd32c84ffe9
-- title:
--   Lemma 3.3 — recursive compression invariants
-- statement:
--   Let $H_1,\ldots,H_k$ be finite-dimensional real Hilbert spaces, $\|M\|_F\le1$, and $\eta>0$. Algorithm 1 has an output, and every such output satisfies, at every cut $j$,
--   $$T_{j-1}=(U_j\otimes I)T_j+E_j,\quad\|T_j\|_F\le1,\quad\dim V_j\le\eta^{-2},$$
--   $$|\langle E_j,u\otimes v\rangle|\le\eta\|u\|\|v\|.$$
--   Here $E_j=((I-U_jU_j^\dagger)\otimes I)T_{j-1}$. The embeddings retain the isometry property from Lemma 3.2. These are conclusions about the actual spectral-selection trace, not hypotheses on arbitrary matrices.
--
--   Differences from the source:
--
--   - encoding: finite-dimensional real Hilbert spaces, indexed from 1 → zero-based row-major Euclidean coordinates, allowing zero-dimensional local spaces; reason: orthonormal coordinates represent every source finite real Hilbert space; positive tensor order is the source convention
--   - encoding: the maps supplied by Lemma 3.2 inside Algorithm 1 → the four displayed invariants together with their inherited column-isometry identity; reason: the source already constructs these maps as isometries; the identity is made explicit for the energy interface
-- source:
--   Martino Bernasconi, Giulio Malavolta, STOC 2027 submission #945 (October 2026), p.12, Lemma 3.3

import Definitions.Def_NuclearTensor_Membership_Optimization

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal

namespace NuclearTensor.Membership

theorem lemma_3_3 (σ : Spectral) (ds : List ℕ) (hk : ds ≠ [])
    (M : Tensor ds) (hM : ‖M‖ ≤ 1) (η : ℝ) (hη : 0 < η) :
    (∃ C : PrefixData ds, algorithm1 σ η M C) ∧
    ∀ C : PrefixData ds, algorithm1 σ η M C → compressionInvariants η C := by sorry

end NuclearTensor.Membership
