-- Prove2me | Theorems.Thm_KingmanSubadditive_Ergodic_theorem_1
-- name    : KingmanSubadditive.Ergodic.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:42:23.718087+00:00
-- url     : https://prove2.me/theorems/0cb9c162-6665-41f2-845b-9e3393ee635a
-- title:
--   Theorem 1: finite limit almost surely and in mean, with E(ξ) = γ
-- statement:
--   Let $x=(x_{st})_{s<t}$ be a subadditive process on a probability space $(\Omega,\mathcal F,P)$, satisfying S₁, full joint stationarity S₂, and S₃. There is an integrable real random variable $\xi$ for which
--   $$\frac{x_{0t}(\omega)}{t}\longrightarrow\xi(\omega)\quad\text{for }P\text{-almost every }\omega,$$
--   $$\int_\Omega\left|\frac{x_{0t}}{t}-\xi\right|\,dP\longrightarrow0,$$
--   and
--   $$E_P(\xi)=\gamma(x)=\inf_{u\ge1}\frac{E_P(x_{0u})}{u}.$$
--   This is Kingman's finite subadditive ergodic theorem. It gives the long-run growth rate even when the shift is not ergodic and the limit is therefore random.
--
--   **Formalization Note** Time is discrete and nonnegative. The limit is real valued; the distinct case allowing a limit of $-\infty$ is Theorem 2, outside this mission.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 885, Theorem 1, (1.2.1)–(1.2.2)

import Mathlib
import Definitions.Def_KingmanSubadditive_Ergodic_Process

namespace KingmanSubadditive.Ergodic

open MeasureTheory Filter Topology

/-- Kingman, *Subadditive ergodic theory*, Ann. Probab. 1(6):883–899 (1973),
p. 885, Theorem 1, (1.2.1)–(1.2.2). `IsSubadditiveProcess` contains the
§1.1 standing conditions S₁, full joint-law stationarity S₂, and S₃.
The limit is real and integrable; convergence in mean is the `L¹`
conjunct, distinct from almost-sure convergence. -/
theorem theorem_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (x : ℕ → ℕ → Ω → ℝ)
    (hx : IsSubadditiveProcess P x) :
    ∃ ξ : Ω → ℝ, Integrable ξ P ∧
      (∀ᵐ ω ∂P, Tendsto (fun t : ℕ => x 0 t ω / (t : ℝ)) atTop (𝓝 (ξ ω))) ∧
      Tendsto (fun t : ℕ => ∫ ω, |x 0 t ω / (t : ℝ) - ξ ω| ∂P) atTop (𝓝 0) ∧
      ∫ ω, ξ ω ∂P = gamma P x := by sorry

end KingmanSubadditive.Ergodic
