-- Prove2me | Theorems.Thm_KawasakiSOS_Threshold_canonical_path_length
-- name    : KawasakiSOS.Threshold.canonical_path_length
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:10:45.753968+00:00
-- url     : https://prove2.me/theorems/e51a9822-ff96-4947-93fe-798470b72c3c
-- title:
--   §4.8: length of the canonical paths
-- statement:
--   There is an absolute constant $C>0$ such that for all $6\le k\le n$ and all $x\ne y$ in $\Omega$ there is a canonical path from $x$ to $y$ with at most $Cnk^3$ edges.
--
--   There are $O(k^2)$ slides, each using at most $3n$ teleports, the opening and closing use $O(n)$ teleports, and each teleport is at most $k/2$ steps. The statement also asserts that a canonical path exists, which is where the mountain climbers theorem enters.
--
--   Differences from the source:
--   - reading: "ℓ = O(nk^3)" → one constant C > 0, quantified before every parameter; reason: the O(·) of the source is read as an absolute constant, uniform in the displayed parameters
--   - reading: ℓ = O(nk³) for the canonical paths → for each x ≠ y a canonical path exists with at most C n k³ edges; reason: the source fixes one canonical path by unspecified tie-breaks, and the bound depends on taking a site sequence of length O(k²), so the path is existential
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), §4.8, Case k ≥ 6, Length, p. 15 (PDF p. 16)

import Mathlib
import Definitions.Def_DiaconisStroock_Poincare_Paths
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_Segment
import Definitions.Def_KawasakiSOS_Threshold_IsCanonicalPath
import Definitions.Def_KawasakiSOS_Threshold_joinStates
open MarkovMixing DiaconisStroock.Poincare

namespace KawasakiSOS.Threshold

/-- Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), §4.8, Case k ≥ 6, Length, p. 15 (PDF p. 16).

Formalization Notes:
- reading: "ℓ = O(nk^3)" → one constant C > 0, quantified before every parameter. The O(·) of the source is read as an absolute constant, uniform in the displayed parameters.
- reading: ℓ = O(nk³) for the canonical paths → for each x ≠ y a canonical path exists with at most C n k³ edges. The source fixes one canonical path by unspecified tie-breaks, and the bound depends on taking a site sequence of length O(k²), so the path is existential. -/
theorem canonical_path_length : ∃ C : ℝ, 0 < C ∧ ∀ (n k : ℕ) [NeZero k], 6 ≤ k → k ≤ n → ∀ x y : Config n k, x ≠ y →
    ∃ (σ : List (ℕ × ℕ)) (segs : List (Segment k × List (Config n k))),
      IsCanonicalPath x y σ segs ∧
        ((pathEdges (joinStates segs)).length : ℝ) ≤ C * (n : ℝ) * (k : ℝ) ^ 3 := by sorry

end KawasakiSOS.Threshold
