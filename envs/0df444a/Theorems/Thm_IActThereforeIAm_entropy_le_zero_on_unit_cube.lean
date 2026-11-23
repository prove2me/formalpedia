-- Prove2me | Theorems.Thm_IActThereforeIAm_entropy_le_zero_on_unit_cube
-- name    : IActThereforeIAm.entropy_le_zero_on_unit_cube
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:03:29.844649+00:00
-- url     : https://prove2.me/theorems/927e7986-a74e-4f77-90b1-a7c5eae06697
-- title:
--   Eq. (19): differential entropy on $(0,1)^d$ is at most $0$, with equality only for the uniform law
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R^d$ carried by the open unit cube $(0,1)^d$. Then its differential entropy satisfies
--
--   $$H(\mu)\le\log\operatorname{Vol}((0,1)^d)=0,$$
--
--   and $H(\mu)=0$ if and only if $\mu$ is the uniform distribution on $(0,1)^d$.
--
--   This is the bound that makes the entropy term of the objective non-positive for encoders into $(0,1)^d$, and it identifies the optimal representation law when $\lambda>1$.
--
--   **Formalization Note** $H(\mu)$ takes the value $-\infty$ when $\mu$ has no Lebesgue density or $f\log f$ is not integrable.
-- source:
--   Liu, Huang and Shi, I Act Therefore I Am: When Is JEPA's Action-Conditioning Enough to Learn Causal Mechanisms?, arXiv:2609.31161v1 (2026), Appendix C (proof of Theorem 2.1), Eq. (19) and the closing remark of the proof, p. 18

import Mathlib
import Definitions.Def_IActThereforeIAm_Basic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace IActThereforeIAm

theorem entropy_le_zero_on_unit_cube {d : ℕ} (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : μ (unitCube d)ᶜ = 0) :
    diffEntropy μ ≤ 0 ∧ (diffEntropy μ = 0 ↔ μ = volume.restrict (unitCube d)) := by sorry

end IActThereforeIAm
