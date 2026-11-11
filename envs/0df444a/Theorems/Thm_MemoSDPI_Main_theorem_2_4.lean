-- Prove2me | Theorems.Thm_MemoSDPI_Main_theorem_2_4
-- name    : MemoSDPI.Main.theorem_2_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:42:16.839627+00:00
-- url     : https://prove2.me/theorems/5ff75491-41db-400e-ad89-49c2836a4c70
-- title:
--   Theorem 2.4 — tensorization: independent copies of an η-SDPI pair satisfy an η-SDPI
-- statement:
--   Let $\eta \in [0,1]$ and let $(V, W)$ be a pair satisfying an $\eta$-SDPI. Let $(V_1, W_1), \dots, (V_d, W_d)$ be independent copies of $(V, W)$. Then
--   $$
--   \big((V_1, \dots, V_d),\ (W_1, \dots, W_d)\big)
--   $$
--   satisfies an $\eta$-SDPI.
--
--   Cited from Polyanskiy–Wu, Proposition 33.11 (stated there for the contraction coefficient $\eta_{\mathrm{KL}}$; the proof applies to the mutual-information form). It takes the SDPI from one coordinate to a whole vector.
--
--   **Formalization Note** The pair is its joint law $\mu$ on $V \times W$ (any measurable spaces). The independent copies have law $\mu^{\otimes d}$ on $(V\times W)^d$, pushed forward to $V^d \times W^d$ by unzipping. The range $\eta \in [0,1]$ of Definition 2.1 is stated as hypotheses.
--
--   Differences from the source:
--   - encoding: independent copies (V_i, W_i) of (V, W) → the product law μ^{⊗d} on Fin d → V × W pushed to (Fin d → V) × (Fin d → W); reason: joint law of the copies; same instances
--   - encoding: η ∈ [0, 1] (Definition 2.1) → hypotheses 0 ≤ η and η ≤ 1; reason: the range is part of Definition 2.1 and is kept as hypotheses of the theorem
-- source:
--   Feldman, Lyu, Talwar, Lower Bounds for Memorization, Privacy and Replicability from Not-So-Strong Data Processing Inequalities, STOC 2027 submission (manuscript sha256 dbb300da…), p. 10, Theorem 2.4

import Mathlib
import Definitions.Def_ThompsonTutorial_InfoRatio_mutualInfo
import Definitions.Def_MemoSDPI_Main_SDPI

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace MemoSDPI.Main

/-- Feldman, Lyu, Talwar, *Lower Bounds for Memorization, Privacy and Replicability from Not-So-Strong Data Processing Inequalities*, STOC 2027 submission (manuscript sha256 dbb300da…), p. 10, Theorem 2.4 (cited from [PW24, Proposition 33.11]): if `(V, W)` satisfies an
`η`-SDPI, then for independent copies `(V_1, W_1), …, (V_d, W_d)` of `(V, W)` the pair
`((V_1, …, V_d), (W_1, …, W_d))` satisfies an `η`-SDPI. -/
theorem theorem_2_4 {V W : Type} [MeasurableSpace V] [MeasurableSpace W]
    (μ : Measure (V × W)) [IsProbabilityMeasure μ] (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (h : SatisfiesSDPI μ η) (d : ℕ) :
    SatisfiesSDPI
      ((Measure.pi fun _ : Fin d => μ).map
        (fun x : Fin d → V × W => ((fun i => (x i).1), (fun i => (x i).2)))) η := by sorry

end MemoSDPI.Main
