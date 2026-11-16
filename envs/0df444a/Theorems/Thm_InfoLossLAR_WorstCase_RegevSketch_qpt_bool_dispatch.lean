-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_qpt_bool_dispatch
-- name    : InfoLossLAR.WorstCase.RegevSketch.qpt_bool_dispatch
-- status  : Open
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T09:01:15.105739+00:00
-- url     : https://prove2.me/theorems/de080210-2247-40be-a5bb-0287f13a9df5
-- title:
--   Exact QPT dispatch controlled by a polynomial-time classical predicate
-- statement:
--   Let $E$ and $A$ be uniform QPT one-bit output circuit families and let $f$ be a total polynomial-time computable string function. There is a uniform QPT family $P$ such that, on every input word $w$, its acceptance probability equals that of $E$ if the first bit of $f(w)$ is true, and equals that of $A$ otherwise (including when $f(w)$ is empty). The equality is exact and is with respect to the platform's Born-rule acceptance probability.
-- source:
--   Standard reversible classical control and uniform quantum circuit composition, formulated using the exact platform predicates IsQPT, PolyTimeComputable, and acceptProb in Definitions.Def_InfoLossLAR_WorstCase_QPT; this is a model-specific composition obligation, not a separate named theorem in Regev.

import Definitions.Def_InfoLossLAR_RegevSketch_DGS

set_option autoImplicit false
open QAlgorithms.Complexity InfoLossLAR.WorstCase

namespace InfoLossLAR.WorstCase.RegevSketch
theorem qpt_bool_dispatch (E A : Family) (hE : IsQPT E) (hA : IsQPT A)
    (f : Str → Str) (hf : PolyTimeComputable f) :
    ∃ P : Family, IsQPT P ∧ ∀ word : Str,
      acceptProb P word = if (f word)[0]? = some true then acceptProb E word else acceptProb A word := by sorry
end InfoLossLAR.WorstCase.RegevSketch
