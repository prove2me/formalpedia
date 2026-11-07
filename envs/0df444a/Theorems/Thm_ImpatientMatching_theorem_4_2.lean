-- Prove2me | Theorems.Thm_ImpatientMatching_theorem_4_2
-- name    : ImpatientMatching.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:50:56.420254+00:00
-- url     : https://prove2.me/theorems/587f0619-79b4-4b35-bf6f-63323350a3f8
-- title:
--   Theorem 4.2 — Finite-Finite hardness
-- statement:
--   Assume the cubic vertex-cover gap of Theorem 4.1. There is a fixed rational constant $\eta>0$ such that the following promise problem is NP-hard. Given a Finite-Finite matching instance with unit rewards and rate-one abandonment on both sides, together with a rational threshold $b>0$, distinguish
--   $$\frac{g^*}{\Lambda}\ge b+\eta\qquad\text{from}\qquad\frac{g^*}{\Lambda}\le b-\eta.$$
--
--   This gives the Finite-Finite part of Theorem 3.2.
--
--   Differences from the source:
--   - reading: Theorem 4.1, cited from [CC06], is used without proof → the hypothesis CubicVCGap; reason: the source does not prove it, and no proof is on the platform; precedent NSWApxHard.Reduction.apx_hardness
--   - reading: the promise problem is NP-hard → the Karp form of the published GapNPHard over every finite nonempty alphabet; reason: §1.3 p.6 defines NP-hard by deterministic polynomial-time many-one reductions
--   - encoding: g∗/Λ ≥ b + η and g∗/Λ ≤ b − η → (b + η)Λ ≤ g∗ and g∗ ≤ (b − η)Λ in EReal, together with 0 < Λ; reason: the source's instances have Λ > 0, which only excludes the empty input, where the ratio is undefined
--   - encoding: independent Poisson streams, one per type; nonanticipating decisions on the observed history and internal randomization → one marked Poisson stream of rate Λ, the published admissible filtration, which also shows the virtual departure times of agents already matched; reason: same law for the arrivals; those extra times are independent of the future, so they act as private randomization
-- source:
--   C. Yan and S. M. Varma, Impatience Makes Matching NP-Hard, manuscript (sha256 7b1051b6c661435675185b0663cb08ab217698a2c4ee07fa0f473686dbb6bed9), Theorem 4.2, (12), p.11

import Definitions.Def_ImpatientMatching_Source
import Definitions.Def_ImpatientMatching_Hardness

namespace ImpatientMatching

/-- **Theorem 4.2 (Finite-Finite hardness).** Yan–Varma, manuscript (sha256 7b1051b6…), (12), p.11: assuming Theorem 4.1, there is a fixed
rational `η > 0` such that it is NP-hard, given a Finite-Finite input with unit rewards and a rational
threshold `b > 0`, to distinguish `g∗/Λ ≥ b + η` from `g∗/Λ ≤ b − η`.

**Formalization Note.** Theorem 4.1 is cited by the source and is the hypothesis `CubicVCGap`. NP-hardness
of the promise problem is the Karp form of the published `GapNPHard`. -/
theorem theorem_4_2 (hCC : CubicVCGap) :
    ∃ η : ℚ, 0 < η ∧ SetCoverThreshold.SetCover.GapNPHard encPromise
      (gapYes Regime.finiteFinite η) (gapNo Regime.finiteFinite η) := by sorry

end ImpatientMatching
