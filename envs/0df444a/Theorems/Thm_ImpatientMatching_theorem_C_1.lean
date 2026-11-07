-- Prove2me | Theorems.Thm_ImpatientMatching_theorem_C_1
-- name    : ImpatientMatching.theorem_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:50:44.7702+00:00
-- url     : https://prove2.me/theorems/6f7a9b23-a602-4eab-89b3-66160a43eefd
-- title:
--   Theorem C.1 — Finite-Zero hardness
-- statement:
--   Assume the cubic vertex-cover gap of Theorem 4.1. There is a fixed rational constant $\eta>0$ such that the following promise problem is NP-hard. Given a Finite-Zero matching instance and a rational threshold $b>0$, distinguish
--   $$\frac{g^*}{\Lambda}\ge b+\eta\qquad\text{from}\qquad\frac{g^*}{\Lambda}\le b-\eta.$$
--
--   This gives the Finite-Zero part of Theorem 3.2.
--
--   Differences from the source:
--   - reading: Theorem 4.1, cited from [CC06], is used without proof → the hypothesis CubicVCGap; reason: the source does not prove it, and no proof is on the platform; precedent NSWApxHard.Reduction.apx_hardness
--   - reading: the promise problem is NP-hard → the Karp form of the published GapNPHard over every finite nonempty alphabet; reason: §1.3 p.6 defines NP-hard by deterministic polynomial-time many-one reductions
--   - encoding: g∗/Λ ≥ b + η and g∗/Λ ≤ b − η → (b + η)Λ ≤ g∗ and g∗ ≤ (b − η)Λ in EReal, together with 0 < Λ; reason: the source's instances have Λ > 0, which only excludes the empty input, where the ratio is undefined
--   - encoding: independent Poisson streams, one per type; nonanticipating decisions on the observed history and internal randomization → one marked Poisson stream of rate Λ, the published admissible filtration, which also shows the virtual departure times of agents already matched; reason: same law for the arrivals; those extra times are independent of the future, so they act as private randomization
-- source:
--   C. Yan and S. M. Varma, Impatience Makes Matching NP-Hard, manuscript (sha256 7b1051b6c661435675185b0663cb08ab217698a2c4ee07fa0f473686dbb6bed9), Theorem C.1, p.29

import Definitions.Def_ImpatientMatching_Source
import Definitions.Def_ImpatientMatching_Hardness

namespace ImpatientMatching

/-- **Theorem C.1 (Finite-Zero hardness).** Yan–Varma, manuscript (sha256 7b1051b6…), p.29: assuming Theorem 4.1, there is a fixed rational
`η > 0` such that it is NP-hard, given a Finite-Zero input and a rational threshold `b > 0`, to
distinguish `g∗/Λ ≥ b + η` from `g∗/Λ ≤ b − η`.

**Formalization Note.** As in `theorem_4_2`. -/
theorem theorem_C_1 (hCC : CubicVCGap) :
    ∃ η : ℚ, 0 < η ∧ SetCoverThreshold.SetCover.GapNPHard encPromise
      (gapYes Regime.finiteZero η) (gapNo Regime.finiteZero η) := by sorry

end ImpatientMatching
