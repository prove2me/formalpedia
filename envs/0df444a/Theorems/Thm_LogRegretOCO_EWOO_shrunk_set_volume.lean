-- Prove2me | Theorems.Thm_LogRegretOCO_EWOO_shrunk_set_volume
-- name    : LogRegretOCO.EWOO.shrunk_set_volume
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:45:35.199071+00:00
-- url     : https://prove2.me/theorems/74b4535d-6ad9-4526-9780-689d1030c7c0
-- title:
--   §3.4 (p. 187): vol(S) = vol(P)/(T+1)^n
-- statement:
--   Let $P \subseteq \mathbb{R}^n$ be any set, $x^* \in \mathbb{R}^n$ and $T \in \mathbb{N}$, and let
--
--   $$
--   S = \Bigl\{ \tfrac{T}{T+1}\, x^* + \tfrac{1}{T+1}\, y \;:\; y \in P \Bigr\}.
--   $$
--
--   Then its Lebesgue measure is
--
--   $$
--   \mathrm{vol}(S) = \frac{\mathrm{vol}(P)}{(T+1)^n}.
--   $$
--
--   Indeed $S$ is a translate of $\frac{1}{T+1}P$, and scaling by $1/(T+1)$ in $n$ dimensions multiplies volume by $(T+1)^{-n}$. In the proof of Theorem 7 this identity converts the lower bound on $S$ into a lower bound on the average over $P$, and it is the source of the factor $n \log(T+1)$ in the regret.
--
--   **Formalization Note** Volumes are Lebesgue (outer) measures in $[0,\infty]$, so the identity holds for every set $P$, including unbounded ones. The paper writes "$S = x^* + \frac{1}{T+1}P$"; the set it defines is the translate of $\frac{1}{T+1}P$ by $\frac{T}{T+1}x^*$, which has the same volume.
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Mach Learn 69 (2007), p. 187, §3.4, proof of Theorem 7 ("vol(S) = vol(P)/(T + 1)^n")

import Mathlib
import Definitions.Def_LogRegretOCO_EWOO_shrunkSet

open MeasureTheory

namespace LogRegretOCO.EWOO

/-- §3.4, p. 187 (Hazan–Agarwal–Kale 2007): the shrunken set `S`, a translate of
`(1/(T+1)) P`, has `vol(S) = vol(P)/(T+1)^n`. -/
theorem shrunk_set_volume (n : ℕ) (P : Set (EuclideanSpace ℝ (Fin n)))
    (xstar : EuclideanSpace ℝ (Fin n)) (T : ℕ) :
    volume (shrunkSet P xstar T) = volume P / ((T : ENNReal) + 1) ^ n := by sorry

end LogRegretOCO.EWOO
