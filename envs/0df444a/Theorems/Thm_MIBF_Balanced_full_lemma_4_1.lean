-- Prove2me | Theorems.Thm_MIBF_Balanced_full_lemma_4_1
-- name    : MIBF.Balanced.full_lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:59:07.783942+00:00
-- url     : https://prove2.me/theorems/4ab69ad4-7437-4d26-9c74-027eca8ae5d9
-- title:
--   [Full] Lemma 4.1 — reflecting one mean about $\tfrac12$ preserves the pure gap $G$
-- statement:
--   Bits throughout. Let $M=(\mu_u,\mu_w,e_u,e_w)$ be a four-moment tuple with $e_u,e_w>0$, and let $G$ be the pure gap $G=L_4-R_\phi$. Then reflecting either mean about $\tfrac12$, keeping its attached entropy, leaves $G$ unchanged:
--   $$G(1-\mu_u,\mu_w,e_u,e_w)=G(\mu_u,\mu_w,e_u,e_w),\qquad G(\mu_u,1-\mu_w,e_u,e_w)=G(\mu_u,\mu_w,e_u,e_w).$$
--   The reflected tuples are again four-moment tuples since $H(1-t)=H(t)$. This symmetry holds for $G$ only, not for $\zeta$ or $\zeta-R_\phi$; it is what allows both means of the pure-gap problem to be placed in $[0,\tfrac12]$.
--
--   Differences from the source:
--   - reading: "preserves $G$, after full relabeling if needed" → the two equalities above for every feasible positive-entropy tuple; reason: $G$ is invariant under full relabeling $(\mu_u,\mu_w,e_u,e_w)\mapsto(\mu_w,\mu_u,e_w,e_u)$ ([Full] (36)), so the relabeling clause adds nothing.
--   - reading: "feasible" → four-moment tuple (Definition 2.1 box); reason: [Full] Lemma 2.1.
-- source:
--   Chen, Gohari, Javanmard, Lin, Mirrokni, Nair, Woodruff, A Proof of the Most Informative Boolean Function Conjecture, arXiv:2609.24931 (held version, sha256 35793b82…1f9f), [Full] = arXiv:2609.24931v2 reproduced in the held PDF, [Full] p. 28 (PDF 50), Lemma 4.1

import Mathlib
import Definitions.Def_MIBF_Balanced_EdgeValue
import Definitions.Def_MIBF_Balanced_PureGap

namespace MIBF.Balanced
theorem full_lemma_4_1 (mu mw eu ew : ℝ) (hM : IsFourMomentTuple mu mw eu ew)
    (heu : 0 < eu) (hew : 0 < ew) :
    pureGap (1 - mu) mw eu ew = pureGap mu mw eu ew ∧
      pureGap mu (1 - mw) eu ew = pureGap mu mw eu ew := by sorry
end MIBF.Balanced
