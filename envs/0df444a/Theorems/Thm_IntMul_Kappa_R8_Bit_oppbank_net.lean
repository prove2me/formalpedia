-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_oppbank_net
-- name    : IntMul.Kappa.R8.Bit.oppbank_net
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T05:30:57.904834+00:00
-- url     : https://prove2.me/theorems/1ebc5981-3aec-4a0e-beac-73b5233b6857
-- title:
--   Opposite-bank QH-network with exact bitR8 child-width moments
-- statement:
--   Jain's round-eight bit witness recompiles the deferred round-seven witness 2 in opposite bank orders: each residual of rank $r$ becomes one contiguous reversed child of width $r$, producing histogram `bitR8` while keeping $W=104719230$ and the same rank sum as `bitR7plain`.
--
--   This problem asks for the corresponding QH-network on Prove2me: numbers $T,q_0$ and a network
--   $$C:\mathrm{QHNet}(\mathbb{Z}/2\mathbb{Z},\,104719230,\,T,\,529)$$
--   such that $C$ runs correctly, the edge and formal checks hold at every large prime power $q^f$, and for all $\tau\in(0,1]$,
--   $$\mathrm{histMoment}(C.\mathrm{hist},529,\tau)=\mathrm{histMoment}(\texttt{bitR8},529,\tau).$$
--
--   Packaging with the proved lemma `BitNetMomStmtG_of_eq` yields `BitNetMomStmtG` at `bitR8`, which is the consequent of `oppbank_mom_of_plain`.
-- source:
--   S. Jain integer-mult-kappa README Round eight bit side; independent/round8-oppbank/; lean/Round8.lean bitHist; Prove2me BitNetMomStmtG_of_eq; parent IntMul.Kappa.R8.Bit.oppbank_mom_of_plain

import Definitions.Def_IntMul_Kappa_RG_Defs
import Definitions.Def_IntMul_KappaJainData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit

open IntMul.Kappa IntMul.Kappa.R6.Bit

/-- Geometric content of Jain's opposite-bank recompile on round-seven witness 2:
there exists a QH-network over `ZMod 2` with $W = 104719230$ roles and width $m = 529$
that runs correctly, passes edge/formal checks at large prime powers, and whose
child-width moments agree exactly with `Jain.bitR8` on $(0,1]$.

(The schedule/frames/payload of the plain witness are unchanged; only address geometry
is recompiled. Formalising that transform on an arbitrary `BitNetMomStmtG` witness is
not required here — this leaf is the constructed network.) -/
theorem oppbank_net :
    ∃ (T : ℕ) (C : QHNet (ZMod 2) 104719230 T 529) (q₀ : ℕ),
      C.RunsOK ∧
        (∀ q, q.Prime → q₀ < q → ∀ f, C.EdgesOK (q ^ f) ∧ C.FormalOK (q ^ f)) ∧
          ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
            histMoment C.hist 529 τ = histMoment Jain.bitR8 529 τ := by
  sorry

end IntMul.Kappa.R8.Bit
