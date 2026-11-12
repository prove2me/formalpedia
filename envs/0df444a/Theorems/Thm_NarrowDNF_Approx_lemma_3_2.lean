-- Prove2me | Theorems.Thm_NarrowDNF_Approx_lemma_3_2
-- name    : NarrowDNF.Approx.lemma_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:16.038699+00:00
-- url     : https://prove2.me/theorems/ae744e02-cfac-4649-84da-14bd6270b862
-- title:
--   Lemma 3.2 — Closure under shifts
-- statement:
--   Let $i$ be a coordinate, let $J$ have increasing local activations, and let $v$ be constant on each adaptive atom of $J$. Then
--   $$U_iv\text{ is }\mathcal F_J\text{-measurable},\qquad L_iv\text{ is }\mathcal F_{J^{\{i\}}}\text{-measurable}.$$
--   Furthermore, for every finite ordered sequence of upper and lower shifts applied to $v$, if $D$ is the set of coordinates at which any lower shift occurs, then the final function is $\mathcal F_{J^D}$-measurable.
--
--   Repeated coordinates are allowed, and $D$ records their union. The forced atom uses original labels, and the sequence retains its specified order. This is the adaptive information closure needed for successive shifts.
--
--   Differences from the source:
--   - encoding: coordinates [n] and bits {0,1} → Fin n and Bool with pointwise false < true; reason: coordinate relabeling preserves all source instances
--   - encoding: local activations and F_J-measurability → functions on S → Bool and constancy on equal dependent-pair atoms; reason: locality and precisely the recorded adaptive information are preserved
--   - encoding: an arbitrary finite sequence with D its lower-coordinate set → a left-folded list of coordinate/Bool choices and its deduplicated lower-coordinate set; reason: every ordered sequence is represented, including repetitions and the empty sequence
-- source:
--   Chenghua Liu, Boning Meng, STOC 2027 submission #1509 (October 2026), Lemma 3.2, p. 6 (PDF p. 7); sequence argument p. 7 (PDF p. 8)

import Definitions.Def_NarrowDNF_Approx_Shifts

namespace NarrowDNF.Approx

theorem lemma_3_2 {n : ℕ} (i : Fin n) (J : ActivationFamily n) (v : Cube n → Bool)
    (hJ : IncreasingActivations J) (hv : AdaptiveMeasurable J v) :
    AdaptiveMeasurable J (upper i v) ∧
    AdaptiveMeasurable (force J {i}) (lower i v) ∧
    (∀ s : List (Fin n × Bool),
      AdaptiveMeasurable (force J (lowerCoordinates s)) (applyShifts s v)) := by sorry

end NarrowDNF.Approx
