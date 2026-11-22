-- Prove2me | Theorems.Thm_MoserSchneckenreither_lemma_4
-- name    : MoserSchneckenreither.lemma_4
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-21T08:57:35.541037+00:00
-- url     : https://prove2.me/theorems/f41d32d8-80eb-4245-a31f-67551beb24b7
-- title:
--   Lemma 3 — Substitution preserves typability
-- statement:
--   Let $\sigma$ be a normalised finite substitution that covers the context $\Gamma$, with a closed typing at the assigned annotation for every context entry. If $\Gamma\vdash^k t:q$, then $t\sigma$ admits a closed typing with result annotation $q$ and some nonnegative rational cost $k\prime$. This uses closed-image consistency.
-- source:
--   Georg Moser and Manuel Schneckenreither, Automated amortised resource analysis for term rewrite systems, Science of Computer Programming 185 (2020), article 102306, https://doi.org/10.1016/j.scico.2019.102306. Section 5, p. 9, Lemma 3. The theorem identifier follows Lemma 4 of arXiv:1811.09071v1.

import Definitions.Def_MoserSchneckenreither_Typing

namespace MoserSchneckenreither

theorem lemma_4 {sig : Signature} {P : Problem sig} (F : AnnotatedSignature P)
    (Γ : Context) (σ : Substitution sig) (hn : σ.Normalised P) (hc : Consistent F σ Γ)
    (t : Term sig) (q : Annotation) (k : ℚ≥0) (ht : Typing F .full Γ k t q) :
    ∃ k' : ℚ≥0, Typing F .full [] k' (t.subst σ.apply) q := by sorry

end MoserSchneckenreither
