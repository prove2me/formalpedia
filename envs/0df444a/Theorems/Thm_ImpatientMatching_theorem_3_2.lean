-- Prove2me | Theorems.Thm_ImpatientMatching_theorem_3_2
-- name    : ImpatientMatching.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:50:55.35154+00:00
-- url     : https://prove2.me/theorems/6b180e1b-6a33-4104-8c4d-112e66ad0d93
-- title:
--   Theorem 3.2 — estimating the optimal throughput within a fixed relative error is NP-hard, in both regimes
-- statement:
--   Assume the cubic vertex-cover gap of Theorem 4.1. For each of the Finite-Finite and Finite-Zero regimes, there exists a universal constant $\delta>0$ such that computing a numerical estimate $\hat g$ satisfying
--   $$|\hat g-g^*|\le\delta g^*$$
--   is NP-hard. Consequently, unless $\mathrm P=\mathrm{NP}$, neither regime admits a polynomial-time approximation scheme for the numerical optimal value.
--
--   Precisely, $\delta$ is chosen for the regime before the language: every NP language over every finite nonempty alphabet maps in polynomial time to an input and a rational threshold $b$, such that any real estimate within $\delta g^*$ decides membership by comparison with $b\Lambda$. A scheme running in polynomial time for each fixed rational accuracy, on all inputs, gives $\mathrm P=\mathrm{NP}$.
--
--   This is the headline hardness result of the paper. It holds even with unit rewards and unit abandonment rates.
--
--   Differences from the source:
--   - reading: Theorem 4.1, cited from [CC06], is used without proof → the hypothesis CubicVCGap; reason: the source does not prove it, and no proof is on the platform; precedent NSWApxHard.Reduction.apx_hardness
--   - reading: computing a numerical estimate is NP-hard → every NP language maps by a deterministic polynomial-time many-one reduction to (I, b) such that every δ-estimate decides membership by comparison with bΛ; reason: this is §1.3 p.6's definition of NP-hardness applied to a search problem, as used on pp.11–12
--   - reading: unless P = NP, neither regime admits a polynomial-time approximation scheme → a scheme, for each fixed rational accuracy, of one polynomial-time algorithm with rational output on every input, implies NP ⊆ P on Cook's classes; reason: P ⊆ NP is standard, so NP ⊆ P is P = NP
--   - encoding: independent Poisson streams, one per type; nonanticipating decisions on the observed history and internal randomization → one marked Poisson stream of rate Λ, the published admissible filtration, which also shows the virtual departure times of agents already matched; reason: same law for the arrivals; those extra times are independent of the future, so they act as private randomization
-- source:
--   C. Yan and S. M. Varma, Impatience Makes Matching NP-Hard, manuscript (sha256 7b1051b6c661435675185b0663cb08ab217698a2c4ee07fa0f473686dbb6bed9), Theorem 3.2, pp.8–9

import Definitions.Def_ImpatientMatching_Source
import Definitions.Def_ImpatientMatching_Hardness

namespace ImpatientMatching

/-- **Theorem 3.2.** Yan–Varma, manuscript (sha256 7b1051b6…), pp.8–9: for each of the Finite-Finite and Finite-Zero regimes there is a universal
constant `δ > 0` such that computing a numerical estimate `ĝ` with `|ĝ − g∗| ≤ δ g∗` is NP-hard.
Consequently, unless `P = NP`, neither regime admits a polynomial-time approximation scheme for the
numerical optimal value.

**Formalization Note.** The source cites its Theorem 4.1 and proves the rest from it, so that theorem is
the hypothesis `CubicVCGap`. The quantifier order is regime, then `δ`, then the NP language. -/
theorem theorem_3_2 (hCC : CubicVCGap) :
    (∀ r : Regime, ∃ δ : ℝ, 0 < δ ∧ EstimationNPHard r δ) ∧
    (∀ r : Regime, AdmitsPTAS r → PEqNP) := by sorry

end ImpatientMatching
