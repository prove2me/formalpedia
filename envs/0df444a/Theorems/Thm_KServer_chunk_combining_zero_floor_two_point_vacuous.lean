-- Prove2me | Theorems.Thm_KServer_chunk_combining_zero_floor_two_point_vacuous
-- name    : KServer.chunk_combining_zero_floor_two_point_vacuous
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-10T09:48:26.292543+00:00
-- url     : https://prove2.me/theorems/76811593-7273-44e1-819c-948b4f2844af
-- title:
--   On two points the hypotheses of the zero-floor regrouping lemma are contradictory
-- statement:
--   The open regrouping lemma `KServer.chunk_combining_zero_floor` asks, for a chunk system $C$ with size floor $0$, size ceiling $c_B$ and Doob jump bound $jb$, that the chunks be regrouped into exactly $M$ chunks with sizes in a window $[c_{\\mathrm{Lo}}',c_{\\mathrm{Hi}}']$ satisfying
--   $$0<c_{\\mathrm{Lo}}'\\le \\mu-(c_B+jb),\\qquad \\mu=\\mathbb E\\Bigl[\\sum_j c_j\\Bigr]/M .$$
--
--   **Statement.** If the underlying metric space has exactly two points $s\\neq t$, this hypothesis package is unsatisfiable: there is no such $C$, $M\\ge1$ and $c_{\\mathrm{Lo}}'>0$.
--
--   **Why.** By two-point rigidity (`KServer.chunk_two_point_expTotal_le`) the expected total mass of a chunk system on a two-point space with size floor $0$ is at most $c_B+jb$. Hence $\\mu\\le (c_B+jb)/M\\le c_B+jb$ and therefore $\\mu-(c_B+jb)\\le0$, which contradicts $0<c_{\\mathrm{Lo}}'\\le\\mu-(c_B+jb)$.
--
--   **Consequence for the mission.** The zero-floor regrouping lemma holds vacuously over two-point metric spaces, so no counterexample to it — and hence no two-point obstruction to the BCR induction at size floor zero — can be built there. Any counterexample must use a metric space with at least three points. (The hypotheses $0\\le jb$ and $0\\le c_B$ are those of the open lemma and are not needed for the contradiction.)

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond

namespace KServer

theorem chunk_combining_zero_floor_two_point_vacuous {X : Type*} [MetricSpace X] {s t : X}
    {cB T pe : ℝ} {mL : ℕ} (C : ChunkSystemB X s t 0 cB T pe mL)
    (hst : s ≠ t) (htwo : ∀ x : X, x = s ∨ x = t)
    {jbS : ℝ} (hjb : C.DoobJumpBound jbS) (hjb0 : 0 ≤ jbS) (hcB : 0 ≤ cB)
    {M : ℕ} (hM0 : 0 < M) {cLo' : ℝ} (hlo0 : 0 < cLo')
    (hlo : cLo' ≤ (∑ ω, C.P ω * ∑ i, C.size ω i) / M - (cB + jbS)) : False := by sorry

end KServer
