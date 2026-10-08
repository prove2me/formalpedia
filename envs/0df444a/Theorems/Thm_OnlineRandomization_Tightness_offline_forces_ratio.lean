-- Prove2me | Theorems.Thm_OnlineRandomization_Tightness_offline_forces_ratio
-- name    : OnlineRandomization.Tightness.offline_forces_ratio
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T07:34:46.39198+00:00
-- url     : https://prove2.me/theorems/233c958a-de1a-4d17-a8f9-a55786c0d936
-- title:
--   §2, p. 13 — in the mates game an adaptive off-line adversary forces every algorithm to pay $M$ while paying $1$
-- statement:
--   Let $t \ge 1$ be an integer and $1 \le m \le M$. In the mates game with parameters $t, m, M$, for every randomized on-line algorithm $K$ there is an adaptive off-line adversary $Q$ such that
--   $$
--   \mathbb E\bigl[c_{K}(Q)\bigr] = M \qquad\text{and}\qquad \mathbb E\bigl[c_Q(K)\bigr] = 1 .
--   $$
--
--   The adversary makes an arbitrary first request, reads the algorithm's answer $a_1$, requests the mate of $a_1$ and stops: the algorithm pays $M$, and the off-line optimum of the two requests is $1$. Hence every on-line algorithm has competitive ratio at least $M$ against adaptive off-line adversaries in this game; this is the second bullet of the tightness claim.
--
--   **Formalization Note.** "Every algorithm" is every randomized on-line algorithm whose coin space is a type in `Type` (deterministic algorithms are the case of a one-point coin space). The adversary's cost is the off-line optimum $c(\underline r)$ of the request sequence, as on p. 8; the hypothesis $1 \le m \le M$ makes that optimum $1$. The game uses the disclosed pin $f_0 = 0$, $f_1 \equiv 1$.
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript p. 13, §2 ("Finally, regardless of how an on-line algorithm chooses a1, ...")

import Mathlib
import Definitions.Def_OnlineRandomization_Tightness_Model
import Definitions.Def_OnlineRandomization_Tightness_MatesGame

namespace OnlineRandomization.Tightness

open MeasureTheory

/-- Manuscript p. 13: in the mates game with `1 ≤ m ≤ M`, against every randomized on-line
algorithm `K` there is an adaptive off-line adversary `Q` (it sets `r₂` to the mate of `a₁`)
whose expected cost is `1` while the algorithm's expected cost is `M`. -/
theorem offline_forces_ratio (t : ℕ) [NeZero t] (m M : ℝ) (hm : 1 ≤ m) (hmM : m ≤ M)
    (Ω : Type) [MeasurableSpace Ω] (K : RandAlg (Fin t × Bool) (Fin t × Bool) Ω) :
    ∃ Q : OfflineAdv (Fin t × Bool) (Fin t × Bool),
      ∫ ω, algCostOffline (matesGame t m M) (K.alg ω) Q ∂K.μ = M ∧
      ∫ ω, advCostOffline (matesGame t m M) (K.alg ω) Q ∂K.μ = 1 := by sorry

end OnlineRandomization.Tightness
