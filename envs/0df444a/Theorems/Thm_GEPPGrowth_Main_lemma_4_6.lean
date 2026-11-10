-- Prove2me | Theorems.Thm_GEPPGrowth_Main_lemma_4_6
-- name    : GEPPGrowth.Main.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:37:55.676883+00:00
-- url     : https://prove2.me/theorems/610962bc-c9b5-4e4b-be30-f73245542f9f
-- title:
--   Lemma 4.6 — Independence of Gaussian QR factors
-- statement:
--   Let $n\ge p$, and $G$ be an $n\times p$ matrix with independent $N(0,1)$ entries. Let the QR
--   decomposition of $G$ be
--
--   $$
--   G=QR
--   $$,
--
--   where $Q^\top Q=I_p$ and $R$ is upper triangular with positive diagonal entries. Then, $Q$ and $R$ are
--   independent.
--
--   This separates the Gaussian QR factors as random variables.
--
--   Differences from the source:
--   - encoding: thin QR factors of the Gaussian matrix with positive diagonal → measurable factor functions of the same input satisfying the QR relation almost surely; reason: random variables are measurable and arbitrary null-set extensions of the unique factors do not change independence
-- source:
--   Daniel Spielman, Xifan Yu, STOC 2027 submission #1176 (October 2026), Lemma 4.6, printed p.9, PDF p.10

import Definitions.Def_GEPPGrowth_Main_Process
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

namespace GEPPGrowth.Main

/-- Lemma 4.6, printed p.9 / PDF p.10. Measurable QR factors of the same Gaussian input, with the relation imposed almost surely; arbitrary null-set extensions do not affect independence. -/
theorem lemma_4_6 (n p : ℕ) (hnp : p ≤ n)
    (Q : Matrix (Fin n) (Fin p) ℝ → Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin n) (Fin p) ℝ → Mat p)
    (hQ : Measurable Q) (hR : Measurable R)
    (hQR : ∀ᵐ G ∂(GaussianMatrix.gaussianMatrix n p), ThinQR G (Q G) (R G)) :
    IndepFun Q R (GaussianMatrix.gaussianMatrix n p) := by sorry

end GEPPGrowth.Main
