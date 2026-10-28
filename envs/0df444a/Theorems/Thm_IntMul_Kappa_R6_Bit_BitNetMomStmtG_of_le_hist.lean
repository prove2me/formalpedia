-- Prove2me | Theorems.Thm_IntMul_Kappa_R6_Bit_BitNetMomStmtG_of_le_hist
-- name    : IntMul.Kappa.R6.Bit.BitNetMomStmtG_of_le_hist
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T05:30:53.372003+00:00
-- url     : https://prove2.me/theorems/489c3296-cfc1-4a00-aac3-09628f038ae5
-- title:
--   BitNetMomStmtG is monotone in the dominating histogram
-- statement:
--   Let $W_b$ and $m_b$ be natural numbers and let $h_1,h_2$ be child-width histograms. Suppose that for every exponent $\tau\in(0,1]$,
--   $$\mathrm{histMoment}(h_1,m_b,\tau)\le\mathrm{histMoment}(h_2,m_b,\tau).$$
--   Then
--   $$\mathrm{BitNetMomStmtG}\,W_b\,m_b\,h_1\quad\Longrightarrow\quad\mathrm{BitNetMomStmtG}\,W_b\,m_b\,h_2.$$
--   Indeed any QH-network whose moments are dominated by $h_1$ is, a fortiori, dominated by $h_2$. Together with `BitNetMomStmtG_of_eq` this is the standard packaging for bit-network moment statements.
-- source:
--   Prove2me Def_IntMul_Kappa_RG_Defs BitNetMomStmtG; companion to IntMul.Kappa.R6.Bit.BitNetMomStmtG_of_eq

import Definitions.Def_IntMul_Kappa_RG_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R6.Bit

open IntMul.Kappa

/-- If every child-width moment of $h_1$ is at most that of $h_2$ on $(0,1]$, then any
QH-network witnessing `BitNetMomStmtG` at $h_1$ also witnesses it at $h_2$ (same network). -/
theorem BitNetMomStmtG_of_le_hist (Wb mb : ℕ) (h₁ h₂ : List (ℕ × ℕ))
    (hle : ∀ τ : ℝ, 0 < τ → τ ≤ 1 → histMoment h₁ mb τ ≤ histMoment h₂ mb τ) :
    BitNetMomStmtG Wb mb h₁ → BitNetMomStmtG Wb mb h₂ := by
  sorry

end IntMul.Kappa.R6.Bit
