-- Prove2me | Theorems.Thm_OffGridStorage_TechChoice_lemma_1_i
-- name    : OffGridStorage.TechChoice.lemma_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:51.832708+00:00
-- url     : https://prove2.me/theorems/077237e9-bfd4-4d17-89a2-ff5656b4e130
-- title:
--   Lemma 1, first bullet, p. 12 — optimal storage is positive iff g > g0
-- statement:
--   Under the standing assumptions, the optimal storage investment of the tracking model is positive if and only if the backup cost exceeds the threshold:
--
--   $$K^*_{TR}>0\iff g>g_0=c_Q+\frac{c_K}{e}+\sqrt{c_Q^2+\frac{2c_Qc_K}{e}} .$$
--
--   Here $K^*_{TR}>0$ means that an optimal tracking plan exists and every optimal tracking plan has strictly positive storage. The threshold does not depend on $T$, $D_H$ or $D_L$.
--
--   This is the key input of Theorem 2: it reduces the comparison of technologies to a comparison of thresholds.
--
--   **Formalization Note** The existence clause keeps "$K>0$ at every optimum" from holding vacuously. At $g=g_0$ the plan $(Q_0,0)$ is optimal, so the right-hand side must be strict, as printed.
-- source:
--   Kaps, Marinesi & Netessine, When Should the Off-grid Sun Shine at Night?, SSRN 3761397 (version of May 11, 2023), p. 12, Lemma 1, first bullet (derivation in Appendix A.4)

import Mathlib
import Definitions.Def_OffGridStorage_TechChoice_Model

namespace OffGridStorage.TechChoice

/-- Lemma 1, first bullet, p. 12: the optimal tracking storage investment is positive iff
`g > g0`. -/
theorem lemma_1_i (p : Params) (hp : Standing p) :
    OptimalStoragePos p ↔ g0 p < p.g := by sorry

end OffGridStorage.TechChoice
