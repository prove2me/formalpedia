-- Prove2me | Theorems.Thm_KMPMixing_proposition_4_7
-- name    : KMPMixing.proposition_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:12:09.295902+00:00
-- url     : https://prove2.me/theorems/68543195-eb51-41ab-a566-74c2a8ade055
-- title:
--   Proposition 4.7 — $1-\lambda_2(M^{(2,G)}_{\mathrm{LKMP}})\ge\frac23(1-\lambda_2(M^{(1,G)}_{\mathrm{KMP}}))$
-- statement:
--   For every connected graph $G=(V=[d],E)$ with $d\ge2$,
--   $$
--   1-\lambda_2\big(M^{(2,G)}_{\mathrm{LKMP}}\big)\ge\frac23\Big(1-\lambda_2\big(M^{(1,G)}_{\mathrm{KMP}}\big)\Big),
--   $$
--   where $\lambda_2$ is the second largest eigenvalue in absolute value.
--
--   Combined with Theorem 4.6 it bounds the labeled mixing time by the single-particle spectral gap.
--
--   Differences from the source:
--   - encoding: every connected graph on $[d]$ → connected `SimpleGraph (Fin d)` with $d\ge2$; reason: with $d=1$ there is no edge and the chains are not defined
--   - encoding: $\lambda_2$ (second largest eigenvalue in absolute value) → `MarkovMixing.lambdaStar`; reason: eigenvalue $1$ is simple for these irreducible chains
-- source:
--   Chen et al., arXiv:2609.38044, Proposition 4.7, p.24 (PDF p.26); restated and proved p.68 (PDF p.70)

import Mathlib
import Definitions.Def_KMPMixing_labeledChain
open MarkovMixing

namespace KMPMixing

/-- **Proposition 4.7** (arXiv:2609.38044, p.24 (PDF p.26); restated and proved p.68 (PDF p.70)).
For every connected graph `G = ([d], E)`,
`1 − λ₂(M^{(2,G)}_LKMP) ≥ (2/3) · (1 − λ₂(M^{(1,G)}_KMP))`.

**Formalization Note** `λ₂` is `MarkovMixing.lambdaStar` (second largest eigenvalue in absolute
value). `M^{(1,G)}_KMP` is the `t = 1` instance of the KMP chain. `d ≥ 2` is added (a graph with
an edge). -/
theorem proposition_4_7 {d : ℕ} (hd : 2 ≤ d) (G : SimpleGraph (Fin d)) [DecidableRel G.Adj]
    (hG : G.Connected) :
    1 - lambdaStar (labeledChain G 2) ≥ 2 / 3 * (1 - lambdaStar (kmpChain G 1)) := by sorry

end KMPMixing
