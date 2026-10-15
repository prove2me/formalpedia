-- Prove2me | Theorems.Thm_LPCommunity_Tight_theorem_2
-- name    : LPCommunity.Tight.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:06:06.385273+00:00
-- url     : https://prove2.me/theorems/dea22ae9-ab4e-45ee-bf3d-cd27da7783ae
-- title:
--   Theorem 2, p. 5 — tightness of the minimum bisection recovery condition
-- statement:
--   Let $n$ be a positive multiple of eight, and let $d_{\mathrm{in}}$ and $d_{\mathrm{out}}$ be nonnegative integers such that $d_{\mathrm{in}}\le n/2-1$, $d_{\mathrm{out}}\le n/2$, and $d_{\mathrm{in}}-d_{\mathrm{out}}\le n/4-1$. Then there is a simple graph $G$ on $n$ vertices and a planted bisection $V_1,V_2$ whose minimum within-side degree is exactly $d_{\mathrm{in}}$ and whose maximum cross-side degree is exactly $d_{\mathrm{out}}$, such that
--
--   $$
--   \text{the minimum bisection problem on }G\text{ does not recover }(V_1,V_2).
--   $$
--
--   This establishes the worst-case tightness of Theorem 1's sufficient condition $d_{\mathrm{in}}-d_{\mathrm{out}}>n/4-1$ within the stated divisibility and degree ranges.
--
--   **Formalization Note** Non-recovery means that a bisection different from both choices of planted side has cut cost no greater than the planted cut. The degree parameters are exact extrema, not bounds. The displayed arithmetic is over real numbers, avoiding truncation of natural-number subtraction.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, p. 5, Theorem 2; proof continues on p. 6

import Mathlib
import Definitions.Def_LPCommunity_MinBisect_Setting

namespace LPCommunity.Tight

/-- Del Pia–Khajavirad–Kunisky, Theorem 2, p. 5. -/
theorem theorem_2 (n din dout : ℕ) (hn : 0 < n) (h8 : 8 ∣ n)
    (hin : (din : ℝ) ≤ (n : ℝ) / 2 - 1)
    (hout : (dout : ℝ) ≤ (n : ℝ) / 2)
    (h : (din : ℝ) - (dout : ℝ) ≤ (n : ℝ) / 4 - 1) :
    ∃ (G : SimpleGraph (Fin n)) (V1 : Finset (Fin n)),
      LPCommunity.MinBisect.IsBisection n V1 ∧ LPCommunity.MinBisect.dIn G V1 = din ∧ LPCommunity.MinBisect.dOut G V1 = dout ∧
      ¬ LPCommunity.MinBisect.MinBisectRecovers G V1 := by sorry

end LPCommunity.Tight
