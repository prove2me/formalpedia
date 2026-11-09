-- Prove2me | Theorems.Thm_MoranYanPAC_Main_structural_exponential_mechanism
-- name    : MoranYanPAC.Main.structural_exponential_mechanism
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T03:06:45.580872+00:00
-- url     : https://prove2.me/theorems/1e4d7bd0-550e-4b7f-8a67-924f2005a746
-- title:
--   Theorem 2 — structural exponential mechanism
-- statement:
--   Let the finite nonempty candidate sets, arbitrary real scores $q_S$, nonnegative integer ranks $\rho$, and the four structural axioms be as in Algorithm 1. Suppose $\Delta>0$, $B\ge1$, $0<\varepsilon\le1$ and $0<\delta<1$. There is a suitable map for every ordered neighboring pair, satisfying fixed-score sensitivity, identity on common outputs and strict rank increase otherwise, the $B^t$ positive-gap preimage bound, and mapped-score preservation, all as specified in Theorem 2.
--
--   Then Algorithm 1 is $(\varepsilon,\delta)$-differentially private on every input. For every dataset $S$ and $0<\beta<1$, its draw $\hat h$ satisfies, with probability at least $1-\beta$,
--
--   $$q_S(\hat h)\ge\max_{h\in\operatorname{Out}(S)}q_S(h)-\frac{2\Delta}{\varepsilon}\left[R_S\log\frac{16B}{\delta}+\log\frac{|\operatorname{Out}(S)|}{\beta}\right].$$
--
--   Here $R_S$ is the rank range on the actual candidates. This provides both the privacy and optimization guarantee used by the general-class learner; no bounded rank height or binary-score specialization is assumed.
--
--   Differences from the source:
--   - encoding: probabilities of the source randomized rules → normalized PMF laws and nonnegative iterated probabilities; reason: the source construction has finite support on each input; distributions on examples remain arbitrary
--   - encoding: ρ(g)=ρ(h)−t at positive integer gap t → ρ(g)+t=ρ(h); reason: addition expresses integer equality without admitting spurious preimages through truncated subtraction
-- source:
--   Shay Moran, Chao Yan, STOC 2027 submission #772 (October 2026), Theorem 2, p. 5 (PDF p. 5)

import Mathlib
import Definitions.Def_MoranYanPAC_Main_StructuralMechanism

set_option autoImplicit false

namespace MoranYanPAC.Main

/-- Theorem 2, p. 5: both privacy and the exact utility bound (2). -/
theorem structural_exponential_mechanism {Z Y : Type*} (M : StructuralData Z Y)
    (ε δ Δ B : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hΔ : 0 < Δ) (hB : 1 ≤ B) (haxioms : StructuralAxioms M Δ B) :
    Private (structuralMechanism M ε δ Δ B) ε δ ∧
    ∀ (S : List Z) (β : ℝ), 0 < β → β < 1 →
      ENNReal.ofReal (1 - β) ≤ eventProbability (structuralMechanism M ε δ Δ B S)
        {h | bestScore M S - (2 * Δ / ε) *
          ((rankRange M S : ℝ) * Real.log (16 * B / δ) +
            Real.log ((M.out S).card / β)) ≤ M.score S h} := by sorry

end MoranYanPAC.Main
