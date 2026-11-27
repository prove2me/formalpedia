-- Prove2me | Theorems.Thm_MultiNashRepair_proposition_4_6_machine
-- name    : MultiNashRepair.proposition_4_6_machine
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T01:57:51.528539+00:00
-- url     : https://prove2.me/theorems/5ee719a1-2692-5573-8606-e5642039c9b5
-- title:
--   Proposition 4.6 (ii) — one Turing machine runs Algorithm 1 in time $B^{O_\sigma(1)}$
-- statement:
--   **Proposition 4.6 (ii): Algorithm 1 runs in time $B^{O_\sigma(1)}$.**
--
--   Fix a rational target $\sigma$ with $1<\sigma<\sigma_\star$ and admissible controls for $\sigma$. There is a single multi-stack Turing machine $M$ over the four-letter alphabet and an exponent $c$ with the following property. On every complete rational payoff table $G$ with $m\ge1$ players, $M$, started on the encoding of $G$, halts within
--   $$c\,(B+2)^c\qquad(B=|\mathrm{enc}(G)|)$$
--   steps with the encoding of a rational profile $x$ with the same action counts that is an output of Algorithm 1. For $m<m_0$, $x$ is a rational initial profile with $\varsigma^{(0)}=m(1-\mathrm{Reg}(x))\ge1$. For $m\ge m_0$, $x$ is the profile of a terminal state reachable by Algorithm 1.
--
--   Both the machine and the exponent are fixed before $m$ and the game, so the bound is uniform in the number of players.
--
--   **Formalization Note.** This is the second conjunct of the milestone `MultiNashRepair.proposition_4_6`; the first conjunct (the iteration bound) is `MultiNashRepair.proposition_4_6_iterations`.
-- source:
--   Tang, Ding, Fang, Breaking the One-Player Extension Barrier, arXiv:2611.06076, Proposition 4.6 (part (ii)), p.14; proof §5.6, pp.43–45

import Mathlib
import Definitions.Def_NashAmplification_Filtering_Encoding
import Definitions.Def_CFLOutliers_OutputsWithin
import Definitions.Def_MultiNashRepair_IDRH

open OnlineCRS.Combine (Sym)
open NashAmplification.Filtering (Table RawProfile encGame encProfile)

namespace MultiNashRepair

theorem proposition_4_6_machine (σ : ℚ) (hσ1 : 1 < σ) (hσ2 : (σ : ℝ) < sigmaStar)
    (ctrl : Controls σ) :
    ∃ (M : Turing.TM2ComputableAux Sym Sym) (c : ℕ), ∀ m : ℕ, 1 ≤ m → ∀ G : Table m,
      ∃ x : RawProfile m, x.sizes = G.sizes ∧
        CFLOutliers.OutputsWithin M (encGame G) (encProfile x) (c * ((encGame G).length + 2) ^ c) ∧
        IDRHOutput ctrl G.utility (x.on G.counts) := by sorry

end MultiNashRepair
