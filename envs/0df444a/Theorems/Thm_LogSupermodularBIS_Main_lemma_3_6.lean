-- Prove2me | Theorems.Thm_LogSupermodularBIS_Main_lemma_3_6
-- name    : LogSupermodularBIS.Main.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:32:44.816317+00:00
-- url     : https://prove2.me/theorems/33ff86d7-c5ac-42b8-995f-d30829cab167
-- title:
--   Lemma 3.6 — variational principle for Boolean guides
-- statement:
--   Let $\mu=e^\Phi/Z_\Phi$ be a strictly positive law on $\{0,1\}^d$, $\Phi(0)=0$. Every Boolean guide $F$ satisfies
--   $$\sum_{i=1}^dE[a(U_i)F_i(U)]+E\Phi(F(U))\le\log Z_\Phi,\tag{3.8}$$
--   with equality if and only if $F=f$ almost everywhere. Thus $\log Z_\Phi$ is the maximum of the left-hand side over Boolean guides, and the unique maximizer is the exact guide (which is itself a Boolean guide).
--
--   Differences from the source: none.
-- source:
--   Jingcheng Liu, Yitong Yin, STOC 2027 submission #1385 (October 2026), p. 16 (PDF 17), Lemma 3.6, (3.8)

import Definitions.Def_LogSupermodularBIS_Main_Variational

open MeasureTheory

set_option autoImplicit false

namespace LogSupermodularBIS.Main

/-- Lemma 3.6 (Variational principle for Boolean guides), p. 16. -/
theorem lemma_3_6 {d : ℕ} (Φ : (Fin d → Bool) → ℝ) (hΦ₀ : Φ (zeroConfig d) = 0) :
    IsBooleanGuide d (exactGuide Φ) ∧
    ∀ F, IsBooleanGuide d F →
      booleanObjective Φ F ≤ Real.log (potentialPartition Φ) ∧
      (booleanObjective Φ F = Real.log (potentialPartition Φ) ↔
        ∀ᵐ u ∂unifCube d, F u = exactGuide Φ u) := by sorry

end LogSupermodularBIS.Main
