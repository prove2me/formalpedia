-- Prove2me | Theorems.Thm_NuclearTensor_Membership_claim_4_4
-- name    : NuclearTensor.Membership.claim_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:18:23.678034+00:00
-- url     : https://prove2.me/theorems/b99ae316-fd81-4045-ba7f-03d5cd91ab46
-- title:
--   Claim 4.4 — terminal objective is 1-Lipschitz
-- statement:
--   Let $\widetilde M\in V\otimes H$ have Frobenius norm at most one, and let $K\subseteq B_H$ be compact and nonempty. For $p\in V$, define $G(p)=\max_{x\in K}\langle\widetilde M,p\otimes x\rangle$. Then
--   $$|G(p)-G(p')|\le\|p-p'\|\qquad(p,p'\in V).$$
--   The Lipschitz constant is exactly one. This is the terminal objective from the proof of Lemma 4.3, with its well-defined maximum domain made explicit.
--
--   Differences from the source:
--
--   - encoding: finite-dimensional real Hilbert spaces, indexed from 1 → zero-based row-major Euclidean coordinates, allowing zero-dimensional local spaces; reason: orthonormal coordinates represent every source finite real Hilbert space; positive tensor order is the source convention
--   - encoding: the well-defined maximum over the compact terminal feasible set → a real supremum over that same set with compactness, nonemptiness, and unit-ball containment explicit; reason: continuity makes the supremum an attained maximum; no new restriction is imposed on a defined source maximum
-- source:
--   Martino Bernasconi, Giulio Malavolta, STOC 2027 submission #945 (October 2026), p.16, Claim 4.4; p.17, proof

import Definitions.Def_NuclearTensor_Membership_Optimization

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal

namespace NuclearTensor.Membership

theorem claim_4_4 (a b : ℕ) (T : Vec (a * b)) (hT : ‖T‖ ≤ 1)
    (K : Set (Vec b)) (hcompact : IsCompact K) (hne : K.Nonempty)
    (hball : K ⊆ unitBall b) :
    LipschitzWith 1 (terminalObjective T K) := by sorry

end NuclearTensor.Membership
