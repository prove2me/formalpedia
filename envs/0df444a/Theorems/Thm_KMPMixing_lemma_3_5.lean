-- Prove2me | Theorems.Thm_KMPMixing_lemma_3_5
-- name    : KMPMixing.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:12:14.289252+00:00
-- url     : https://prove2.me/theorems/4e2a66b2-7faf-4776-8bc3-697c091f40a0
-- title:
--   Lemma 3.5 — unlabeling does not increase the distance to stationarity
-- statement:
--   Let $G=(V=[d],E)$ be a connected graph on $d\ge2$ vertices and $t$ a positive integer. Let $x\in\Omega_G$ and $r=(\#_1(x),\dots,\#_d(x))\in\Delta_G$. Then for every $k\ge0$,
--   $$
--   \big\|M^k_{\mathrm{KMP}}(r,\cdot)-\pi_{\mathrm{KMP}}\big\|_{\mathrm{TV}}\le\big\|M^k_{\mathrm{LKMP}}(x,\cdot)-\pi_{\mathrm{LKMP}}\big\|_{\mathrm{TV}}.
--   $$
--
--   Mixing bounds for the labeled chain therefore transfer to the KMP chain.
--
--   Differences from the source:
--   - encoding: a connected graph $G=(V=[d],E)$ → `G : SimpleGraph (Fin d)` with `G.Connected`, vertex $i$ ↦ index $i-1$; reason: same graphs
-- source:
--   Chen et al., arXiv:2609.38044, Lemma 3.5, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_KMPMixing_labeledChain
open MarkovMixing

namespace KMPMixing

/-- **Lemma 3.5** (arXiv:2609.38044, p.17 (PDF p.19)). Let `G = ([d], E)` be a connected graph on
`d ≥ 2` vertices and `t` a positive integer. Let `x ∈ Ω_G` and `r = (#_1(x), …, #_d(x)) ∈ Δ_G`.
Then for every `k ≥ 0`,
`‖M^k_KMP(r, ·) − π_KMP‖_TV ≤ ‖M^k_LKMP(x, ·) − π_LKMP‖_TV`. -/
theorem lemma_3_5 {d : ℕ} (hd : 2 ≤ d) (G : SimpleGraph (Fin d)) [DecidableRel G.Adj]
    (hG : G.Connected) (t : ℕ) (ht : 0 < t) (x : Fin t → Fin d) (k : ℕ) :
    tvDist (rowDist (kmpChain G t) k (unlabel x)) (uniformDist (State d t)) ≤
      tvDist (rowDist (labeledChain G t) k x) (labeledStationary d t) := by sorry

end KMPMixing
