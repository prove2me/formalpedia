-- Prove2me | Theorems.Thm_Levin2003_tilingExpansion_simulates_polyTime
-- name    : Levin2003.tilingExpansion_simulates_polyTime
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-20T22:02:06.841055+00:00
-- url     : https://prove2.me/theorems/c451f2ea-dd2a-45ba-88a3-5397679d3198
-- title:
--   Tiling Expansion simulates every polynomial-time length-preserving function
-- statement:
--   For every polynomial-time computable, length-preserving function $f$ there are polynomial-time computable maps $\mathrm{enc}$ and $\mathrm{dec}$, with $\mathrm{enc}$ injective, such that
--
--   $$\mathrm{dec}\big(\textsf{TilingExpansion}(\mathrm{enc}(w))\big) = f(w) \quad \text{for every } w.$$
--
--   This is the tiling step of the reduction of Section 4.3: *'we reduce the computation of the UTM, modified as above, to Tiling in a standard way. We add a special border symbol and restrict the tiles so that it can combine only with the input or output alphabets (of equal size), or with the end-tape symbol, or the state initiating the computation, depending on the sides of the tile. The expansion concept does the rest.'* A computation is laid out row by row in the square, the top line encoding the initial configuration, and expansion fills the square deterministically because each successive cell admits exactly one permitted tile.
--
--   This milestone is the correctness half of the reduction only. It does not by itself transfer hardness, since that additionally requires the encoding not to distort the uniform distribution on instances by more than a polynomial factor.
-- source:
--   L. A. Levin, The Tale of One-Way Functions, Problems of Information Transmission 39(1), 2003, pp. 92-103 (translated from Problemy Peredachi Informatsii, No. 1, 2003, pp. 103-117); preprint https://arxiv.org/abs/cs/0012023, Section 4.3, p. 102 ('The reduction')

import Definitions.Def_Levin2003_tiling_expansion

namespace Levin2003

/-- Tiling Expansion simulates every polynomial-time computable
length-preserving function through polynomial-time encoding and decoding maps,
the encoding being injective. -/
theorem tilingExpansion_simulates_polyTime :
    ∀ f : Bits → Bits, PolyTimeComputable f → LengthPreserving f →
      ∃ enc dec : Bits → Bits, PolyTimeComputable enc ∧ PolyTimeComputable dec ∧
        Function.Injective enc ∧ ∀ w : Bits, dec (tilingExpansion (enc w)) = f w := by
  sorry

end Levin2003
