-- Prove2me | Theorems.Thm_IIDMatchHard_proposition_3_2
-- name    : IIDMatchHard.proposition_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:06:18.192578+00:00
-- url     : https://prove2.me/theorems/938a5bd0-3fc3-4943-bb25-dcd3330cdfe4
-- title:
--   Proposition 3.2 (Alimonti–Kann) — Max Cut on cubic graphs is hard to approximate
-- statement:
--   There is a constant $\eta_0\in(0,1)$ such that approximating the maximum cut $C(G)$ within a factor $1\pm\eta_0$ is NP-hard, even when $G$ is a simple cubic graph.
--
--   The paper cites this from P. Alimonti and V. Kann, *Some APX-completeness results for cubic graphs*, Theoret. Comput. Sci. 237 (2000). It is the starting point of the reduction proving Theorem 3.1.
--
--   Differences from the source:
--   - reading: "approximating C(G) within a factor 1 ± η0 is NP-hard" → ApproxNPHard encGraph IsCubic C η0: a one-query polynomial-time reduction from every NP language, correct for every rational answer within the factor; reason: the same reading of NP-hardness as in Theorem 3.1; the one-query form follows from the gap form of the cited L-reduction
--   - encoding: a simple cubic graph → a GraphInput (a SimpleGraph on Fin N) encoded by encGraph, with every vertex having three neighbors; reason: Lean convention; same graphs
-- source:
--   Teng, Yang, Computational Hardness of Online Stochastic Matching (manuscript of Nov. 3, 2026, sha256 f0193d92…), Proposition 3.2, p.5 (PDF p.6)

import Definitions.Def_IIDMatchHard_ApproxNPHard
import Definitions.Def_IIDMatchHard_Cut
import Definitions.Def_NSWApxHard_Reduction_CubicVC

set_option autoImplicit false

open NSWApxHard.Reduction

namespace IIDMatchHard

/-- **Proposition 3.2 ([Alimonti and Kann, 2000]).** There is a constant `η₀ ∈ (0, 1)` such that
approximating `C(G)` within a factor `1 ± η₀` is NP-hard, even when `G` is a simple cubic graph.
Teng, Yang, *Computational Hardness of Online Stochastic Matching* (manuscript of Nov. 3, 2026,
sha256 f0193d92…), Proposition 3.2, p.5 (PDF p.6), citing P. Alimonti, V. Kann, *Some APX-completeness
results for cubic graphs*, Theoret. Comput. Sci. 237 (2000).

**Formalization Note.** Graphs are `GraphInput`s (simple graphs on `Fin N`, encoded by
`encGraph`); cubic means every vertex has three neighbors. "NP-hard" is `ApproxNPHard`, the same
one-query reading as in Theorem 3.1. -/
theorem proposition_3_2 :
    ∃ η0 : ℝ, 0 < η0 ∧ η0 < 1 ∧
      ApproxNPHard encGraph (fun H => IsCubic H.G) (fun H => (maxCut H.G : ℝ)) η0 := by sorry

end IIDMatchHard
