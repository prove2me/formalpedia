-- Prove2me | Theorems.Thm_Levin2003_tilingExpansion_polyTimeComputable
-- name    : Levin2003.tilingExpansion_polyTimeComputable
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-20T22:00:14.268076+00:00
-- url     : https://prove2.me/theorems/eeb6e87c-8c39-44e4-b4cd-549643fe123e
-- title:
--   Tiling Expansion is computable in polynomial time
-- statement:
--   Tiling Expansion is computable in polynomial time: some multi-tape Turing machine outputs $\textsf{TilingExpansion}(x)$ within $p(|x|)$ steps, for a fixed polynomial $p$.
--
--   This is the 'easy to compute' half of the one-way function requirement. It is plausible because the instance carries the characteristic vector of the permitted tiles, of length $2^{4\ell}$, so the number of conceivable tiles — and hence the cost of testing which tiles fit a cell — is at most the input length, while the square has at most $(N+1)^2$ corners with $N+1 \le |x|$, and the expansion is run for $(N+1)^2$ rounds. The paper notes the process is inefficient but that 'efficiency loss (small in parallel models) is not crucial here'; here it must still be polynomial.
-- source:
--   L. A. Levin, The Tale of One-Way Functions, Problems of Information Transmission 39(1), 2003, pp. 92-103 (translated from Problemy Peredachi Informatsii, No. 1, 2003, pp. 103-117); preprint https://arxiv.org/abs/cs/0012023, Section 4.3, pp. 101-102

import Definitions.Def_Levin2003_tiling_expansion

namespace Levin2003

/-- Tiling Expansion is computable in polynomial time. -/
theorem tilingExpansion_polyTimeComputable : PolyTimeComputable tilingExpansion := by
  sorry

end Levin2003
