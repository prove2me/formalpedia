-- Prove2me | Theorems.Thm_GrothendieckLB_lemma_10_2
-- name    : GrothendieckLB.lemma_10_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:53:27.916518+00:00
-- url     : https://prove2.me/theorems/4d748ab9-88e8-46e1-a662-6d457c243c99
-- title:
--   Lemma 10.2: optimality of the inverse-majorant bound
-- statement:
--   There exist odd analytic limiting mixed correlation functions $H_k$ and admissible values $\gamma_k$ for them such that
--   $$
--   \gamma_k\le\frac\pi{2K_G}\quad\text{and}\quad\gamma_k\longrightarrow\frac\pi{2K_G},
--   $$
--   and equivalently the resulting upper bounds satisfy
--   $$
--   \frac\pi{2\gamma_k}\longrightarrow K_G .
--   $$
--   So after allowing mixtures and increasing dimension the inverse-majorant bound is asymptotically optimal. Combined with Proposition 9.2 this gives $\pi/(2K_G)\le11/12$.
--
--   **Formalization Note** $K_G$ is the published `GrothendieckConstant.grothendieckConst`. The "odd analytic" of the lemma is carried both as explicit clauses and inside `IsAdmissible`.
--
--   Differences from the source:
--   - encoding: limiting mixed schemes as a probability distribution on pairs of sign functions → MixedScheme, jointly measurable random pairs over a probability space; reason: the paper's proof uses finite mixtures of step functions, which are such random pairs
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Lemma 10.2, p.42

import Mathlib
import Definitions.Def_GrothendieckLB_IsAdmissible
import Definitions.Def_GrothendieckLB_IsLimitingMixed
import Definitions.Def_GrothendieckConstantDefs
open Filter Topology

namespace GrothendieckLB

/-- Lemma 10.2, optimality of the inverse-majorant bound (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Lemma 10.2, p.42): there exist odd
analytic limiting mixed correlation functions `H_k` and admissible values `γ_k` with
`γ_k ≤ π/(2K_G)` and `γ_k → π/(2K_G)`; equivalently, `π/(2γ_k) → K_G`.

**Formalization Note** `K_G` is the published `GrothendieckConstant.grothendieckConst`. -/
theorem lemma_10_2 :
    ∃ (H : ℕ → ℝ → ℝ) (γ : ℕ → ℝ),
      (∀ k, (∀ᶠ t in 𝓝 (0 : ℝ), H k (-t) = -H k t) ∧ AnalyticAt ℝ (H k) 0 ∧
        IsLimitingMixed (H k) ∧ IsAdmissible (H k) (γ k) ∧
        γ k ≤ Real.pi / (2 * GrothendieckConstant.grothendieckConst)) ∧
      Tendsto γ atTop (𝓝 (Real.pi / (2 * GrothendieckConstant.grothendieckConst))) ∧
      Tendsto (fun k => Real.pi / (2 * γ k)) atTop
        (𝓝 GrothendieckConstant.grothendieckConst) := by sorry

end GrothendieckLB
