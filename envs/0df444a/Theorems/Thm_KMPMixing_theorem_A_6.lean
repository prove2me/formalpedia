-- Prove2me | Theorems.Thm_KMPMixing_theorem_A_6
-- name    : KMPMixing.theorem_A_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:11:23.590551+00:00
-- url     : https://prove2.me/theorems/79d66fdb-ae3a-40e3-8e8c-f9b8d111f239
-- title:
--   Theorem A.6 — $1-\lambda_2(M^{(2,G)}_{\mathrm{KMP}})\ge\frac{2(d+1)}{3d}\,(1-\lambda_2(M^{(1,G)}_{\mathrm{KMP}}))$
-- statement:
--   For every connected graph $G=(V=[d],E)$ with $d\ge2$,
--   $$
--   1-\lambda_2\big(M^{(2,G)}_{\mathrm{KMP}}\big)\ge\frac{2(d+1)}{3d}\Big(1-\lambda_2\big(M^{(1,G)}_{\mathrm{KMP}}\big)\Big),
--   $$
--   where $\lambda_2$ is the second largest eigenvalue in absolute value.
--
--   It compares the symmetric block of the two-particle labeled chain with the single-particle walk. The source's proof goes through the continuous KMP chain and the external result [KQS25, Theorem 1.1] (Lemma 5.3).
--
--   Differences from the source:
--   - encoding: every connected graph on $[d]$ → connected `SimpleGraph (Fin d)` with $d\ge2$; reason: with $d=1$ there is no edge and the chains are not defined
--   - encoding: $\lambda_2$ (second largest eigenvalue in absolute value) → `MarkovMixing.lambdaStar`; reason: eigenvalue $1$ is simple for these irreducible chains, so the two agree
-- source:
--   Chen et al., arXiv:2609.38044, Theorem A.6, p.66 (PDF p.68)

import Mathlib
import Definitions.Def_KMPMixing_kmpChain
open MarkovMixing

namespace KMPMixing

/-- **Theorem A.6** (arXiv:2609.38044, p.66 (PDF p.68)). For every connected graph
`G = ([d], E)`,
`1 − λ₂(M^{(2,G)}_KMP) ≥ (2(d + 1)/(3d)) · (1 − λ₂(M^{(1,G)}_KMP))`.

**Formalization Note** `λ₂` is `MarkovMixing.lambdaStar` (second largest eigenvalue in absolute
value, p.66). `M^{(1,G)}_KMP` is the `t = 1` instance of the KMP chain. `d ≥ 2` is added (a
graph with an edge). The paper's proof uses Lemma 5.3, which is [KQS25, Theorem 1.1]. -/
theorem theorem_A_6 {d : ℕ} (hd : 2 ≤ d) (G : SimpleGraph (Fin d)) [DecidableRel G.Adj]
    (hG : G.Connected) :
    1 - lambdaStar (kmpChain G 2) ≥
      (2 * ((d : ℝ) + 1)) / (3 * (d : ℝ)) * (1 - lambdaStar (kmpChain G 1)) := by sorry

end KMPMixing
