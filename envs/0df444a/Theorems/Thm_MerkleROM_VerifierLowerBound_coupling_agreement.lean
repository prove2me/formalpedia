-- Prove2me | Theorems.Thm_MerkleROM_VerifierLowerBound_coupling_agreement
-- name    : MerkleROM.VerifierLowerBound.coupling_agreement
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T22:33:39.546851+00:00
-- url     : https://prove2.me/theorems/7d94b47d-c34f-4593-a9a4-01c18b487df2
-- title:
--   Lemma 6.2 — Agreement conditional on a good leaf
-- statement:
--   Fix the normalized bounded-depth decision tree of Section 6, a supported good leaf $\tau$, and any collection of distinct internal vertices $v_i$ on its path. Let $y_i$ be the ideal answers on that path and $\mu_{v_i}$ the transition law computed from good-prefix probabilities. Under the specified greedy coupling,
--
--   $$\Pr[\forall i\in I,\ R(\ell(v_i))=y_i\mid\mathrm{ideal\ leaf}=\tau]=\prod_{i\in I}\min\left\{\frac{2^{-\lambda}}{\mu_{v_i}(y_i)},1\right\}.$$
--
--   The empty collection is included, with probability and empty product equal to one. The input domain $X$ is arbitrary. Supported goodness supplies every positive conditioning mass.
--
--   This gives exact conditional agreement for any subset of the path queries.
--
--   Differences from the source:
--   - encoding: a good leaf of the normalized Section 6 tree → a supported good leaf with no repeated path query and all outputs queried; reason: these are the stated local proof conventions, guarantee positive conditional masses, and are absent from the main product lemma
--   - encoding: full real and ideal oracles in the coupling → the joint law of the ideal leaf and real answers along its path; reason: finite query-cylinder events determine the asserted probability even for infinite X; reverse greedy sampling is explicitly given on p.25
-- source:
--   Miranda Christ, Oliver Korten, Tal Malkin, Noam Mazor, Shyamal Patel, STOC 2027 submission #1169 (October 2026), Merkle Trees Minimize Verifier Complexity in the ROM, p. 25, Lemma 6.2. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1169.pdf

import Definitions.Def_MerkleROM_VerifierLowerBound_protocol
import Definitions.Def_MerkleROM_VerifierLowerBound_product

set_option autoImplicit false
noncomputable section

namespace MerkleROM.VerifierLowerBound

theorem coupling_agreement {X : Type} {lam t : ℕ}
    (D : Tree X (Bits lam) (Fin t → Finset X)) (V : SetVerifier X lam) (k : ℕ)
    (hD : ProductNormalized D) (tau : ProductLeaf X lam t)
    (htau : tau ∈ (freshLeaves D).support) (hgood : GoodLeaf V k tau)
    (I : Finset (Fin tau.2.length)) :
    conditionalAgreement D V k tau I =
      ∏ i ∈ I, min ((2 : ℝ)^(-(lam : ℤ)) /
        mu D V k ((tau.2.map Prod.snd).take i.val) (tau.2[i.val]).2) 1 := by sorry

end MerkleROM.VerifierLowerBound
