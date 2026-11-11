-- Prove2me | Theorems.Thm_LogSupermodularBIS_Main_proposition_3_8
-- name    : LogSupermodularBIS.Main.proposition_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:32:59.137199+00:00
-- url     : https://prove2.me/theorems/fd40f69b-0416-4065-83d8-93b533713bff
-- title:
--   Proposition 3.8 — exactness and concavity of the relaxation
-- statement:
--   Let $\Phi$ be a potential on $\{0,1\}^d$ normalized by $\Phi(0)=0$. Every guide $F$ satisfies $\mathcal P(F)\le\log Z_\Phi$, with equality if and only if $F=f$ almost everywhere. The objective $\mathcal P$ is concave on the convex set of guides if and only if $\Phi$ is supermodular, that is, if and only if $\mu$ is log-supermodular.
--
--   Differences from the source: none.
-- source:
--   Jingcheng Liu, Yitong Yin, STOC 2027 submission #1385 (October 2026), p. 18 (PDF 19), Proposition 3.8

import Definitions.Def_LogSupermodularBIS_Main_Variational

open MeasureTheory

set_option autoImplicit false

namespace LogSupermodularBIS.Main

/-- Proposition 3.8 (Exactness and concavity of the relaxation), p. 18. -/
theorem proposition_3_8 {d : ℕ} (Φ : (Fin d → Bool) → ℝ) (hΦ₀ : Φ (zeroConfig d) = 0) :
    (∀ F, IsGuide d F → variationalObjective Φ F ≤ Real.log (potentialPartition Φ)) ∧
    (∀ F, IsGuide d F → (variationalObjective Φ F = Real.log (potentialPartition Φ) ↔
        ∀ᵐ u ∂unifCube d, F u = exactGuide Φ u)) ∧
    (ConcaveOn ℝ (guides d) (variationalObjective Φ) ↔ Supermodular Φ) := by sorry

end LogSupermodularBIS.Main
