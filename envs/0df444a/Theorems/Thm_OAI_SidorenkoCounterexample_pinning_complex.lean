-- Prove2me | Theorems.Thm_OAI_SidorenkoCounterexample_pinning_complex
-- name    : OAI.SidorenkoCounterexample.pinning_complex
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-08T16:54:39.01955+00:00
-- url     : https://prove2.me/theorems/0335b463-3182-492e-bb30-3345ea8ea92c
-- title:
--   Scores uniquely pin the incidence pattern to its identity assignment
-- statement:
--   Let $I=\mathrm{Fin}(13)$, $J=\mathrm{Fin}(22)$, and $E=\mathrm{Fin}(22)\times\mathrm{Fin}(3)$ be the points, faces, and incidence corners of the prescribed pattern. Write $t:E\to I$ for the point of a corner and $h:E\to J$ for its face.
--
--   There exist real vertex weights $L,R$ and real pair weights $P$ such that the assignment score
--   $$
--   S(a,b)=\sum_{i\in I}L_{a(i)}+\sum_{j\in J}R_{b(j)}
--          +\sum_{e\in E}P_{a(t(e)),\,b(h(e))}
--   $$
--   satisfies
--   $$
--   S(a,b)<S(\mathrm{id}_I,\mathrm{id}_J)
--   \qquad\text{for every }(a,b)\ne(\mathrm{id}_I,\mathrm{id}_J).
--   $$
--   The quantification includes all maps $a:I\to I$ and $b:J\to J$, without injectivity requirements. This finite pinning property is the score interface used by the exponential weighting step of the kernel construction.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Pinning.lean#L117, lemma pinning_complex, with the score defined in Dilution.lean. The original statement and its quantification over all assignment maps are preserved.

import Mathlib
import Definitions.Def_SidorenkoPinningScores
open OAI.SidorenkoCounterexample

theorem OAI.SidorenkoCounterexample.pinning_complex : ∃ s : VertexPairScores (Fin 13) (Fin 22),
    ∀ a b,(a,b)≠(id,id) → s.score cornerPoint (fun k : ActCorner => k.1) a b < s.score cornerPoint (fun k : ActCorner => k.1) id id := by sorry
