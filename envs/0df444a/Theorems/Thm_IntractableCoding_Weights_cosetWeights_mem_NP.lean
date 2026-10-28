-- Prove2me | Theorems.Thm_IntractableCoding_Weights_cosetWeights_mem_NP
-- name    : IntractableCoding.Weights.cosetWeights_mem_NP
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:27:14.423832+00:00
-- url     : https://prove2.me/theorems/9c86c636-4400-424f-8363-5c7d3619181d
-- title:
--   Section III, p. 385 — COSET WEIGHTS is in NP
-- statement:
--   The language of encoded COSET WEIGHTS yes-instances is in NP: there are a Boolean verifier $V(c,s)$, computed by a polynomial-time multi-stack Turing machine, and a polynomial $p$ such that for every binary string $s$,
--   $$s=\mathrm{enc}(A,y,w)\text{ for some yes-instance}\iff\exists c\in\{0,1\}^*,\ |c|\le p(|s|)\ \text{and}\ V(c,s)=1.$$
--
--   The natural certificate is the vector $x$ itself; the verifier must also reject strings that encode no instance.
--
--   Differences from the source:
--   - encoding: the input is encoded into a binary string of length N → encodeCoset / encodeSubspace: row and column counts in unary, the entries of A (and y) bit by bit, w in binary with a self-delimiting marker code; reason: a fixed honest encoding is part of any precise NP statement; unary dimensions keep the certificate length (the number of rows) polynomial in the input length, binary w is the shorter (stricter) choice for membership and changes nothing for hardness, since the reductions output w = n and w = 3n² + 4n
--   - reading: NP-complete, described heuristically in Section II (a polynomial-time algorithm for the problem would give one for every NP-problem) → in NP = PolynomiallyVerifiable (a polynomial-time TM2 verifier with polynomially long certificates) on the encoded language; NP-hard = every polynomially verifiable language over every alphabet many-one reduces to the problem by a map computed by a polynomial-time TM2 machine; reason: the paper refers to Karp [4] and Garey–Johnson [3] for the precise notion, which is many-one (Karp) reducibility; both of the paper's constructions are many-one maps, and many-one hardness implies the Turing-style sentence of the paper
-- source:
--   Berlekamp, McEliece & van Tilborg, On the Inherent Intractability of Certain Coding Problems, IEEE Trans. Inform. Theory IT-24(3), 1978, https://doi.org/10.1109/TIT.1978.1055873, p. 385, Section III ("It is easy to see that both COSET WEIGHTS and SUBSPACE WEIGHTS are in NP.")

import Mathlib
import Definitions.Def_IntractableCoding_Weights_NPComplete
import Definitions.Def_IntractableCoding_Weights_Problems

namespace IntractableCoding.Weights

/-- COSET WEIGHTS is in NP: the set of binary strings `encodeCoset I` with `I` a
yes-instance has a polynomial-time TM2 verifier with polynomially long certificates. -/
theorem cosetWeights_mem_NP :
    PricingWithTips.PolynomiallyVerifiable (languageOf encodeCoset CosetWeightsYes) := by sorry

end IntractableCoding.Weights
