-- Prove2me | Theorems.Thm_NonuniformCompetitive_Snoopy_Supplement_theorem_2
-- name    : NonuniformCompetitive.Snoopy.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:01:13.255809+00:00
-- url     : https://prove2.me/theorems/58a2852c-190b-41e7-91d5-2c67ba7be689
-- title:
--   Theorem 2 — phase LP bound implies global competitiveness
-- statement:
--   Let $T$ be a finite directed task system, $s_0$ its initial state, and $A$ a phase-based randomized causal algorithm for the phase system of §2, including causal deletion that is free and state-preserving for A and leaves the offline work profile unchanged. Complete phases start and end at known optimal states, have positive finite optimal costs and form a finite alphabet; every nonempty final incomplete phase is a prefix of one of them. Suppose $\alpha$ is the attained finite minimum of the phase LP, whose phase constraints are
--   $$\mathbb E C_A(\rho)\le\alpha C_{\rm opt}(\rho)+\Phi_{\rm start(\rho)}-\Phi_{\rm finish(\rho)}.$$
--   Then $A$ is globally $\alpha$-competitive:
--   $$\exists a\in\mathbb R\ \forall\sigma:\quad \mathbb E C_A(\sigma)\le\alpha C_{\rm opt}(\sigma)+a.$$
--   The finite additive constant covers the initial potentials and any unfinished final phase. The theorem concerns actual causal task algorithms and their costs, rather than arbitrary numbers with a telescoping inequality.
--
--   Differences from the source:
--   - encoding: finite task systems with either look-ahead convention → finite S,R with directed finite transition costs, possibly infinite processing costs and separate before/moment/after actions; reason: these are the general objects of §2, not a symmetric metric specialization
--   - generalization: deleted requests are free and state-preserving for every algorithm in the restricted class → deleted requests are free and state-preserving for the chosen A and preserve the offline work profile; reason: Theorem 2 only needs those two deletion properties; the source universal property implies them, so every source instance is included
--   - encoding: finite bounded phases and a phase-based randomized algorithm → a reachable finite alphabet, causal phase parser, incomplete-prefix extension and equality of primitive-action laws with local policies; reason: these encode actual actions and the source forgetting condition without postulating a global cost inequality
--   - encoding: the LP bound and competitive conclusion → an attained finite LP minimum and a real additive constant on every finite feasible input; reason: the source minimizes the LP; infeasible words are not assigned zero optimal cost by toReal
--   - encoding: phase endpoints satisfy Theorem 1’s witness conditions and phase algorithms forget preceding phases → forcing witnesses only at listed endpoints, initialized local policies and equality of primitive-action laws; reason: p.547 requires endpoint witnesses, not witnesses for every unused state or normalization at every internal known prefix
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), DOI 10.1007/BF01189993, p. 547, Theorem 2

import Mathlib
import Definitions.Def_NonuniformCompetitive_Snoopy_Supplement_phaseSystem

namespace NonuniformCompetitive.Snoopy.Supplement

/-- Theorem 2, p.547 (proof continues p.548). The finite directed task model,
causal filtering, known-state boundaries and bounded incomplete phase are those
of §2. The LP bound is its attained finite minimum, with potential sign
Φ_start − Φ_finish. The conclusion is global competitiveness with one additive
constant; no competitiveness inequality is part of IsPhaseBased. -/
theorem theorem_2 {S R : Type} [Fintype S] [Fintype R] [LinearOrder S]
    (T : TaskSystem S R) (s₀ : S) (F : PhaseSystem T s₀) (hF : F.Valid)
    (localPolicy : S → TaskRandomized T) (A : TaskRandomized T)
    (hA : IsPhaseBased F localPolicy A) (α : ℝ)
    (hLP : IsPhaseLPBound T
      (fun q : {q : TaskPhase S R // q ∈ F.alphabet} => q.val) localPolicy α) :
    A.Competitive s₀ α := by sorry

end NonuniformCompetitive.Snoopy.Supplement
