-- Prove2me | Theorems.Thm_KMPMixing_lemma_A_7
-- name    : KMPMixing.lemma_A_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:12:20.869661+00:00
-- url     : https://prove2.me/theorems/3313209c-a67b-4fea-a339-615066621204
-- title:
--   Lemma A.7 — $\lambda_1(C|_{\mathcal H_{\mathrm{Asym}}})=\lambda_2(M^{(1,G)}_{\mathrm{KMP}})$
-- statement:
--   For every connected graph $G=(V=[d],E)$ with $d\ge2$,
--   $$
--   \lambda_1\big(C|_{\mathcal H_{\mathrm{Asym}}}\big)=\lambda_2\big(M^{(1,G)}_{\mathrm{KMP}}\big).
--   $$
--
--   The antisymmetric block of the two-particle labeled chain is controlled exactly by the single-particle walk.
--
--   Differences from the source:
--   - encoding: every connected graph on $[d]$ → connected `SimpleGraph (Fin d)` with $d\ge2$; reason: with $d=1$ there is no edge and the chains are not defined
--   - encoding: $\lambda_2$ (second largest eigenvalue in absolute value) → `MarkovMixing.lambdaStar`; reason: eigenvalue $1$ is simple for this irreducible chain
-- source:
--   Chen et al., arXiv:2609.38044, Lemma A.7, p.67 (PDF p.69)

import Mathlib
import Definitions.Def_KMPMixing_kmpChain
import Definitions.Def_KMPMixing_lambdaOneAsym
open MarkovMixing

namespace KMPMixing

/-- **Lemma A.7** (arXiv:2609.38044, p.67 (PDF p.69)). For every connected graph `G = ([d], E)`,
`λ₁(C|_{𝓗_Asym}) = λ₂(M^{(1,G)}_KMP)`.

**Formalization Note** `λ₁(C|_{𝓗_Asym})` is `lambdaOneAsym G`; `λ₂` is `MarkovMixing.lambdaStar`
of the `t = 1` KMP chain. `d ≥ 2` is added (a graph with an edge). -/
theorem lemma_A_7 {d : ℕ} (hd : 2 ≤ d) (G : SimpleGraph (Fin d)) [DecidableRel G.Adj]
    (hG : G.Connected) :
    lambdaOneAsym G = lambdaStar (kmpChain G 1) := by sorry

end KMPMixing
