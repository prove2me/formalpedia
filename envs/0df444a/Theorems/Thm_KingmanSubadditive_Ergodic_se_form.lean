-- Prove2me | Theorems.Thm_KingmanSubadditive_Ergodic_se_form
-- name    : KingmanSubadditive.Ergodic.se_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:42:25.551978+00:00
-- url     : https://prove2.me/theorems/13285abf-64cd-4561-b2b6-6e8d82840f96
-- title:
--   (1.3.4)–(1.3.5): almost sure and mean convergence under Sᴱ
-- statement:
--   Suppose $\theta$ preserves the probability measure $P$ and the integrable functions $f_n$ satisfy Sᴱ. Then there is an integrable real random variable $\xi$ such that
--   $$\frac{f_n(\omega)}n\longrightarrow\xi(\omega)\quad\text{for }P\text{-almost every }\omega,$$
--   and
--   $$\int_\Omega\left|\frac{f_n}{n}-\xi\right|\,dP\longrightarrow0.$$
--   This is the measure-preserving formulation of the convergence claims of Theorem 1.
--
--   **Formalization Note** The transformation is neither assumed invertible nor ergodic. The conclusion is for the full integer sequence $n\to\infty$.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 886, §1.3, (1.3.4)–(1.3.5)

import Mathlib
import Definitions.Def_KingmanSubadditive_Ergodic_SE

namespace KingmanSubadditive.Ergodic

open MeasureTheory Filter Topology

/-- Kingman, *Subadditive ergodic theory*, Ann. Probab. 1(6):883–899 (1973),
p. 886, §1.3, (1.3.4)–(1.3.5). `IsSE` contains (1.3.2)–(1.3.3) and
measure preservation; the map need not be invertible or ergodic. -/
theorem se_form {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (θ : Ω → Ω) (f : ℕ → Ω → ℝ)
    (hf : IsSE P θ f) :
    ∃ ξ : Ω → ℝ, Integrable ξ P ∧
      (∀ᵐ ω ∂P, Tendsto (fun n : ℕ => f n ω / (n : ℝ)) atTop (𝓝 (ξ ω))) ∧
      Tendsto (fun n : ℕ => ∫ ω, |f n ω / (n : ℝ) - ξ ω| ∂P) atTop (𝓝 0) := by sorry

end KingmanSubadditive.Ergodic
