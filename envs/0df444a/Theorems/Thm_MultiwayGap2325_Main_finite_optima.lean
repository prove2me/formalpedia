-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_finite_optima
-- name    : MultiwayGap2325.Main.finite_optima
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:06:09.495566+00:00
-- url     : https://prove2.me/theorems/b1c38d73-6c24-470d-a432-ba69bcf55a21
-- title:
--   §1 — finite integral and CKR optima are attained
-- statement:
--   Let $k\ge2$ and let $I$ be a finite $k$-terminal instance. The sets of integral and fractional feasible objective values are nonempty and bounded below. Each has a feasible minimizer, and
--   $$
--   0\le\operatorname{LP}(I)\le\operatorname{OPT}(I),\qquad
--   \operatorname{LP}(I)=0\ \Longrightarrow\ \operatorname{OPT}(I)=0.
--   $$
--   These conclusions discharge the well-posedness obligations behind the actual optimization values in the goal. Minimizers are conclusions, rather than freely supplied data constrained to have desired values.
--
--   Differences from the source:
--   - encoding: an arbitrary finite undirected graph with distinct terminals → a graph on Fin n with Fin k terminals and an ordered edge list; reason: all finite vertex types admit reindexing; opposite orientations aggregate and loops have zero cost; neither n nor real weights are bounded
--   - encoding: the minimum integral cost OPT and the optimum LP of (2) → sInf of the actual feasible objective sets, with a separate attainment and boundedness obligation; reason: both sets are nonempty and bounded below for k≥2, and their optima are attained; these facts are conclusions of finite_optima, not assumptions in the goal
--   - encoding: the ratio OPT/LP in the supremum of gaps → OPT/LP when LP is positive and gap 1 when LP=0; reason: LP=0 implies OPT=0 and a positive-LP instance of gap 1 exists for every k≥2; gap_sequence_well_posed states equality of the two suprema
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), §1, p. 1, equations (1),(2), and p. 2 definition of the integrality gap

import Definitions.Def_MultiwayGap2325_Main_FiniteGap

namespace MultiwayGap2325.Main

/-- Optimization well-posedness for the finite graphs of §1, pp.1–2. -/
theorem finite_optima {n k : ℕ} (hk : 2 ≤ k)
    (I : MultiwayCut.Instance (Fin n) k) :
    (integralValues I).Nonempty ∧ BddBelow (integralValues I) ∧
    (fractionalValues I).Nonempty ∧ BddBelow (fractionalValues I) ∧
    (∃ c : Fin n → Fin k, MultiwayCut.IsFeasibleLabeling I c ∧
      MultiwayCut.cutWeight I c = integralOpt I) ∧
    (∃ x : Fin n → Fin k → ℝ, MultiwayCut.IsFeasibleEmbedding I x ∧
      MultiwayCut.relaxValue I x = fractionalOpt I) ∧
    0 ≤ fractionalOpt I ∧ fractionalOpt I ≤ integralOpt I ∧
    (fractionalOpt I = 0 → integralOpt I = 0) := by sorry

end MultiwayGap2325.Main
