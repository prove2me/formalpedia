-- Prove2me | Theorems.Thm_IntractableCoding_Weights_coset_subspace_weights_npComplete
-- name    : IntractableCoding.Weights.coset_subspace_weights_npComplete
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:27:13.998457+00:00
-- url     : https://prove2.me/theorems/2647e42a-d4a9-4c73-8630-2b562cc20c24
-- title:
--   Abstract and Section III, pp. 384–386 — COSET WEIGHTS and SUBSPACE WEIGHTS are NP-complete
-- statement:
--   Both coding problems of the paper are NP-complete:
--
--   1. **COSET WEIGHTS** — given a binary matrix $A$, a binary vector $y$ and a nonnegative integer $w$, is there a row vector $x$ of Hamming weight $|x|\le w$ with $xA=y$ over $\mathrm{GF}(2)$? — is in NP and NP-hard;
--   2. **SUBSPACE WEIGHTS** — given a binary matrix $A$ and a nonnegative integer $w$, is there a row vector $x$ of Hamming weight exactly $w$ with $xA=0$ over $\mathrm{GF}(2)$? — is in NP and NP-hard.
--
--   Here "in NP" means the language of encoded yes-instances has a polynomial-time Turing-machine verifier with polynomially long certificates, and "NP-hard" means every language in NP reduces to the problem by a polynomial-time computable many-one reduction.
--
--   COSET WEIGHTS is the decision version of decoding a general binary linear code from its syndrome; SUBSPACE WEIGHTS asks whether a binary linear code, given by a parity-check matrix, has a codeword of a given weight. Their NP-completeness is the reason no general efficient decoding or weight-enumeration algorithm is expected.
--
--   Differences from the source:
--   - encoding: the input is encoded into a binary string of length N → encodeCoset / encodeSubspace: row and column counts in unary, the entries of A (and y) bit by bit, w in binary with a self-delimiting marker code; reason: a fixed honest encoding is part of any precise NP statement; unary dimensions keep the certificate length (the number of rows) polynomial in the input length, binary w is the shorter (stricter) choice for membership and changes nothing for hardness, since the reductions output w = n and w = 3n² + 4n
--   - encoding: binary matrix A, row vector x, xA computed mod 2 → Matrix (Fin m) (Fin n) (ZMod 2), Matrix.vecMul x A, Hamming weight hammingNorm; reason: GF(2) = ZMod 2; xA with x indexed by the rows is Matrix.vecMul
--   - reading: NP-complete, described heuristically in Section II (a polynomial-time algorithm for the problem would give one for every NP-problem) → in NP = PolynomiallyVerifiable (a polynomial-time TM2 verifier with polynomially long certificates) on the encoded language; NP-hard = every polynomially verifiable language over every alphabet many-one reduces to the problem by a map computed by a polynomial-time TM2 machine; reason: the paper refers to Karp [4] and Garey–Johnson [3] for the precise notion, which is many-one (Karp) reducibility; both of the paper's constructions are many-one maps, and many-one hardness implies the Turing-style sentence of the paper
-- source:
--   Berlekamp, McEliece & van Tilborg, On the Inherent Intractability of Certain Coding Problems, IEEE Trans. Inform. Theory IT-24(3), 1978, https://doi.org/10.1109/TIT.1978.1055873, p. 384, Abstract; p. 385, Section III ("This proves that COSET WEIGHTS is NP-complete."); p. 386, Section III ("This shows that SUBSPACE WEIGHTS is NP-complete, as asserted.")

import Mathlib
import Definitions.Def_IntractableCoding_Weights_NPComplete
import Definitions.Def_IntractableCoding_Weights_Problems

namespace IntractableCoding.Weights

/-- COSET WEIGHTS and SUBSPACE WEIGHTS are both NP-complete: each is in NP and NP-hard under
polynomial-time TM2 many-one reductions, for the binary encodings `encodeCoset` and
`encodeSubspace`. -/
theorem coset_subspace_weights_npComplete :
    NPCompleteFor encodeCoset CosetWeightsYes ∧
      NPCompleteFor encodeSubspace SubspaceWeightsYes := by sorry

end IntractableCoding.Weights
