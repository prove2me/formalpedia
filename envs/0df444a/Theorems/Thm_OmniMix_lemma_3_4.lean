-- Prove2me | Theorems.Thm_OmniMix_lemma_3_4
-- name    : OmniMix.lemma_3_4
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T01:40:01.327491+00:00
-- url     : https://prove2.me/theorems/88f6899f-c63f-4369-b801-6ad84ef1b332
-- title:
--   Lemma 3.4 — $F^\eta_{p,y}(h)\le1+S^\eta_p(h)(y-p)$
-- statement:
--   Let $p\in[0,1]$, $y\in\{0,1\}$, $h\in[-1,1]$ and $0<\eta\le1/2$. With $F^\eta_{p,y}(h)=\exp(\eta h(y-p)-\eta^2p(1-p)h^2)$ and $S^\eta_p(h)=F^\eta_{p,1}(h)-F^\eta_{p,0}(h)$,
--   $$
--   F^\eta_{p,y}(h)\le1+S^\eta_p(h)\,(y-p).
--   $$
--
--   This linearizes the weight factor of Algorithm 2 in the outcome, which is what lets the EVI step control the growth of the total weight.
--
--   Differences from the source: none.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, Lemma 3.4, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_OmniMix_Feta
import Definitions.Def_OmniMix_Seta
import Definitions.Def_OmniMix_outVal

namespace OmniMix

/-- **Lemma 3.4.** Liu–Luo–Ratliff, arXiv:2610.41023, §3.2, p.14: "For any `p ∈ [0, 1]`, `y ∈ {0, 1}`, `h ∈ [−1, 1]`, and
`0 < η ≤ 1/2`, define `F^η_{p,y}(h) = exp(ηh(y − p) − η²p(1 − p)h²)` and
`S^η_p(h) = F^η_{p,1}(h) − F^η_{p,0}(h)`. We have `F^η_{p,y}(h) ≤ 1 + S^η_p(h)(y − p)`." -/
theorem lemma_3_4 (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (y : Bool) (h : ℝ) (hh0 : -1 ≤ h)
    (hh1 : h ≤ 1) (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1 / 2) :
    Feta η p (outVal y) h ≤ 1 + Seta η p h * (outVal y - p) := by sorry

end OmniMix
