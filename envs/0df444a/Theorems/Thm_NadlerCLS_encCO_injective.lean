-- Prove2me | Theorems.Thm_NadlerCLS_encCO_injective
-- name    : NadlerCLS.encCO_injective
-- status  : Proved
-- author  : @utkuokur
-- created : 2026-11-12T19:54:12.694211+00:00
-- url     : https://prove2.me/theorems/9ee7c423-77c9-4f2b-b232-3e8a5b96158d
-- title:
--   The binary code of a Continuous-LocalOpt instance determines the instance
-- statement:
--   An instance of Continuous-LocalOpt, or of $\beta$-Hölder-LocalOpt, on the cube $[0,1]^n$ is a tuple $I=(f,p,\delta,\lambda)$ consisting of two arithmetic circuits $f$ and $p$ and two rational parameters $\delta$ and $\lambda$. Its binary code is the concatenation
--
--   $$
--   \operatorname{enc}(I)\;=\;\operatorname{enc}(f)\,\operatorname{enc}(p)\,\operatorname{enc}(\delta)\,\operatorname{enc}(\lambda),
--   $$
--
--   where a circuit is coded as its list of gates followed by its list of output gates, and every number is written in a self-delimiting binary code.
--
--   The lemma states that this code is injective: for all instances $I$ and $J$ of the same dimension $n$,
--
--   $$
--   \operatorname{enc}(I)=\operatorname{enc}(J)\;\Longrightarrow\; I=J .
--   $$
--
--   The search problems of this mission are stated on binary strings: a string is a valid input if it is the code of some valid instance, and the answers to a string are defined through an instance having that code. Injectivity says that this instance is unique, which is what a reduction needs when it translates an answer for a constructed instance back to the original one, as in Theorems C.2 and C.3 and Lemmas C.6 and C.8 of the paper.
--
--   Differences from the source:
--   - auxiliary statement: the paper does not state this fact; it identifies an instance with its binary description (Section 2, p.7: "all numerical parameters are rational and represented in binary").
--
--   **Formalization Note** The code is `encCO`, built from the public codes `encNat`, `encRat`, `encList` and `gateCode`, and the instance type is `COInstance n`. The statement holds for every `n` and assumes no validity of the instances.
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101v4 (3 Nov 2026), https://arxiv.org/abs/2609.14101, Section 2 (Notation and computational model), p.7; auxiliary lemma for the formalization of the reductions of Appendix C (Theorem C.3, pp.36–37). Not stated in the paper.

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_NadlerCLS_COInstance

set_option autoImplicit false

namespace NadlerCLS

open NetworkEquilibriumCLS.LinearNash

/-- **The instance code is injective** (auxiliary lemma for the reductions of
Xiong–Vlatakis-Gkaragkounis, *On the Complexity of Finding Fixed Points for Set-Valued
Contractions*, arXiv:2609.14101v4, Appendix C; Section 2, p.7: "all numerical parameters are
rational and represented in binary"). Two instances `(f, p, δ, λ)` with the same binary code
`encCO` are equal.

**Formalization Note** Not stated in the paper, which identifies an instance with its binary
description. No validity assumption is needed, and `n` is arbitrary. -/
theorem encCO_injective (n : ℕ) :
    Function.Injective (encCO : COInstance n → List Bool) := by sorry

end NadlerCLS
