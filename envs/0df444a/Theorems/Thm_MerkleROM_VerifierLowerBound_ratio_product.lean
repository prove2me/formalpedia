-- Prove2me | Theorems.Thm_MerkleROM_VerifierLowerBound_ratio_product
-- name    : MerkleROM.VerifierLowerBound.ratio_product
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T22:33:28.810207+00:00
-- url     : https://prove2.me/theorems/2068eaec-4743-4aed-a804-b8253e124dd9
-- title:
--   Lemma 6.3 — Product of path likelihood ratios
-- statement:
--   For a supported good leaf $\tau=y_1\cdots y_m$ of the normalized tree, let $\delta$ be the actual probability of a good leaf under the original uniform execution, and put $r_i=2^{-\lambda}/\mu_{v_i}(y_i)$. Then
--
--   $$\prod_{i=1}^{m}r_i=\delta.$$
--
--   The ratios and $\delta$ are computed from the tree and its good-leaf event. They are not arbitrary parameters constrained by a product hypothesis. The identity also includes an empty root-to-leaf path.
--
--   This relates local path likelihood ratios to the original search success probability.
--
--   Differences from the source:
--   - encoding: a good leaf of the normalized Section 6 tree → a supported good leaf with no repeated path query and all outputs queried; reason: these are the stated local proof conventions, guarantee positive conditional masses, and are absent from the main product lemma
-- source:
--   Miranda Christ, Oliver Korten, Tal Malkin, Noam Mazor, Shyamal Patel, STOC 2027 submission #1169 (October 2026), Merkle Trees Minimize Verifier Complexity in the ROM, p. 26, Lemma 6.3. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1169.pdf

import Definitions.Def_MerkleROM_VerifierLowerBound_protocol
import Definitions.Def_MerkleROM_VerifierLowerBound_product

set_option autoImplicit false
noncomputable section

namespace MerkleROM.VerifierLowerBound

theorem ratio_product {X : Type} {lam t : ℕ}
    (D : Tree X (Bits lam) (Fin t → Finset X)) (V : SetVerifier X lam) (k : ℕ)
    (hD : ProductNormalized D) (tau : ProductLeaf X lam t)
    (htau : tau ∈ (freshLeaves D).support) (hgood : GoodLeaf V k tau) :
    (∏ i : Fin tau.2.length, pathRatio D V k tau i) = goodProbability D V k := by sorry

end MerkleROM.VerifierLowerBound
