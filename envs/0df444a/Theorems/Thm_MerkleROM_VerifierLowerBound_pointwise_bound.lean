-- Prove2me | Theorems.Thm_MerkleROM_VerifierLowerBound_pointwise_bound
-- name    : MerkleROM.VerifierLowerBound.pointwise_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T22:34:02.662404+00:00
-- url     : https://prove2.me/theorems/0ecaf5e2-07c4-4a28-87b0-69280e2a2291
-- title:
--   Lemma 6.4 — Pointwise disjoint-product bound
-- statement:
--   Let $t>0$ and let $\tau=y_1\cdots y_m$ be a supported good leaf of the normalized Section 6 tree, with $t$ disjoint accepted output sets $W_j$ of size at most $k$. Define $r_i=2^{-\lambda}/\mu_{v_i}(y_i)$, $I_j=\{i:\ell(v_i)\in W_j\}$, $a_j(\tau)=\prod_{i\in I_j}\min\{1,r_i\}$ and let $\delta$ be the actual good-leaf probability. Then
--
--   $$\frac1t\sum_{j=1}^{t}a_j(\tau)\ge e^{-k}\delta^{1/t}\exp\left(-\frac1t\sum_{i=1}^{m}(r_i-1)\right).$$
--
--   The final exponential factor is retained pointwise, including paths with ratios exceeding one. All these quantities are derived from the original tree and its ideal conditioning.
--
--   This is the complete pointwise estimate used in the disjoint product analysis.
--
--   Differences from the source:
--   - encoding: a good leaf of the normalized Section 6 tree → a supported good leaf with no repeated path query and all outputs queried; reason: these are the stated local proof conventions, guarantee positive conditional masses, and are absent from the main product lemma
--   - encoding: reciprocals 1/t in Section 6.2 → 0<t on this local pointwise statement; reason: the source uses a uniform choice among t outputs and 1/t; t=0 remains included in Lemma 6.1
-- source:
--   Miranda Christ, Oliver Korten, Tal Malkin, Noam Mazor, Shyamal Patel, STOC 2027 submission #1169 (October 2026), Merkle Trees Minimize Verifier Complexity in the ROM, p. 27, Lemma 6.4. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1169.pdf

import Definitions.Def_MerkleROM_VerifierLowerBound_protocol
import Definitions.Def_MerkleROM_VerifierLowerBound_product

set_option autoImplicit false
noncomputable section

namespace MerkleROM.VerifierLowerBound

theorem pointwise_bound {X : Type} {lam t : ℕ}
    (D : Tree X (Bits lam) (Fin t → Finset X)) (V : SetVerifier X lam) (k : ℕ)
    (ht : 0 < t) (hD : ProductNormalized D) (tau : ProductLeaf X lam t)
    (htau : tau ∈ (freshLeaves D).support) (hgood : GoodLeaf V k tau) :
    (1/(t : ℝ)) * (∑ j : Fin t, pathAgreement D V k tau j) ≥
      Real.exp (-(k : ℝ)) * (goodProbability D V k)^(1/(t : ℝ)) *
        Real.exp (-(1/(t : ℝ)) * (∑ i : Fin tau.2.length, (pathRatio D V k tau i-1))) := by sorry

end MerkleROM.VerifierLowerBound
