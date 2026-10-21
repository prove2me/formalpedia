-- Prove2me | Theorems.Thm_IntMul_Kappa_R6_Bit_BitNetMomStmtG_of_eq
-- name    : IntMul.Kappa.R6.Bit.BitNetMomStmtG_of_eq
-- status  : Proved
-- author  : @Ethan
-- created : 2026-10-21T05:16:21.016987+00:00
-- url     : https://prove2.me/theorems/43926340-a616-4496-8ad1-a04319264671
-- title:
--   Package a checked QHNet with exact histogram moments into BitNetMomStmtG
-- statement:
--   **Packaging lemma for moment-dominated bit networks.**
--
--   Let $W_b$, $m_b$, $T$ and $q_0$ be natural numbers, let $h_b$ be a child-width histogram, and let
--   $$C:\mathrm{QHNet}(\mathbb{Z}/2\mathbb{Z},\,W_b,\,T,\,m_b)$$
--   be a bit network such that:
--
--   1. $C$ runs correctly;
--   2. for every prime $q>q_0$ and every exponent $f$, the edge and formal checks hold at $q^f$;
--   3. for every $\tau\in(0,1]$,
--      $$\mathrm{histMoment}(C.\mathrm{hist},\,m_b,\,\tau)=\mathrm{histMoment}(h_b,\,m_b,\,\tau).$$
--
--   Then $\mathrm{BitNetMomStmtG}\,W_b\,m_b\,h_b$ holds.
--
--   This is the final packaging step of the proved round-six argument `bitNetR6_mom` (where exact moment equality is weakened to $\le$). It lets round-seven/eight bit-network constructions reduce to (i) producing a checked network and (ii) matching histogram moments, without re-unfolding the `BitNetMomStmtG` predicate.
--
--   **Formalization Note.** `BitNetMomStmtG` and `QHNet` are from `IntMul_Kappa_RG_Defs`.
-- source:
--   Prove2me IntMul.Kappa.R6.Bit.NB.bitNetR6_mom (submission packaging `mom_eq.le` into BitNetR6MomStmt / BitNetMomStmtG); Def_IntMul_Kappa_RG_Defs

import Definitions.Def_IntMul_Kappa_RG_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R6.Bit

open IntMul.Kappa

/-- If a concrete QH-network runs correctly, passes edge/formal checks at large prime powers,
and its child-width moments agree exactly with a target histogram `hb`, then `BitNetMomStmtG`
holds for `(Wb, mb, hb)`. This is the packaging step used at the end of
`bitNetR6_mom` (`mom_eq.le`). -/
theorem BitNetMomStmtG_of_eq (Wb mb T q₀ : ℕ) (hb : List (ℕ × ℕ))
    (C : QHNet (ZMod 2) Wb T mb)
    (hRun : C.RunsOK)
    (hOK : ∀ q, q.Prime → q₀ < q → ∀ f, C.EdgesOK (q ^ f) ∧ C.FormalOK (q ^ f))
    (hmom : ∀ τ : ℝ, 0 < τ → τ ≤ 1 → histMoment C.hist mb τ = histMoment hb mb τ) :
    BitNetMomStmtG Wb mb hb := by
  sorry

end IntMul.Kappa.R6.Bit
