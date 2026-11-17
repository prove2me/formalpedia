-- Prove2me | Theorems.Thm_ManolescuPiccirillo_exists_zero_surgery_counterexample
-- name    : ManolescuPiccirillo.exists_zero_surgery_counterexample
-- status  : Open
-- author  : @Lucas
-- created : 2026-11-16T18:52:46.780263+00:00
-- url     : https://prove2.me/theorems/361b0a4c-3c6a-49c6-b4c6-17f7533553c6
-- title:
--   A certified Manolescu–Piccirillo $0$-surgery counterexample pair
-- statement:
--   There exist two knot diagrams $K_1,K_2$ (valid, single-component, in normal form) such that: (1) their $0$-framed links are Kirby equivalent, i.e. $K_1$ and $K_2$ are $0$-friends with the same $0$-surgery; (2) $K_1$ admits a slice-disk movie, certifying that $K_1$ is slice; and (3) the Rasmussen $s$-invariant of $K_2$ is non-zero, certifying that $K_2$ is not slice. By the trace embedding lemma and Freedman's theorem, such a pair yields an exotic $4$-sphere, disproving the smooth $4$-dimensional Poincaré conjecture. This is exactly the certificate checked by the FrontierMath verifier.
-- source:
--   Epoch AI FrontierMath, smooth 4D Poincaré conjecture, https://epoch.ai/frontiermath/open-problems/smooth-poincare-4d ; Manolescu–Piccirillo, https://arxiv.org/abs/2102.04391

import Mathlib
import Definitions.Def_ManolescuPiccirillo_PD
import Definitions.Def_ManolescuPiccirillo_Kirby
import Definitions.Def_ManolescuPiccirillo_Movie
import Definitions.Def_ManolescuPiccirillo_Lee1
import Definitions.Def_ManolescuPiccirillo_Lee2

namespace ManolescuPiccirillo
theorem exists_zero_surgery_counterexample :
    ∃ (K₁ K₂ : PD), K₁.IsKnot ∧ K₂.IsKnot ∧ K₁.NormalForm ∧ K₂.NormalForm ∧
      KirbyEquivalent (FramedLink.zero K₁) (FramedLink.zero K₂) ∧
      HasSliceMovie K₁ ∧ K₂.rasmussenS ≠ 0 := by sorry
end ManolescuPiccirillo
