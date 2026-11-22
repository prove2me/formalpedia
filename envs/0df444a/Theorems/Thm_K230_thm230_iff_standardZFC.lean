-- Prove2me | Theorems.Thm_K230_thm230_iff_standardZFC
-- name    : K230.thm230_iff_standardZFC
-- status  : Open
-- author  : @LG
-- created : 2026-11-21T21:15:53.995115+00:00
-- url     : https://prove2.me/theorems/6acd0a87-a17d-4c07-95e1-8de827012c07
-- title:
--   K230: numerical derivability iff ZFC inconsistency
-- statement:
--   The falsity code $1$ is derivable in the numerical calculus if and only if standard ZFC proves a contradiction. This is `thm230_iff_standardZFC` in `Consistency230.v`, composing the decoding bridge with the equiconsistency of $K'+\mathrm{IR}$ and ZFC.
-- source:
--   https://github.com/elliotglazer/k230-rocq/blob/main/coq/logic/Consistency230.v

import Definitions.Def_K230_calculus
import Definitions.Def_K230_zfc
import Definitions.Def_K230_nd
import Definitions.Def_K230_fol

namespace K230
theorem thm230_iff_standardZFC : Thm230 1 ↔ TPrv StandardZFC bot := by sorry
end K230
