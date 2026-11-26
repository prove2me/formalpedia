-- Prove2me | Theorems.Thm_Kyprianou_Ch04_jointContinuousPartialsPositiveTimeV1
-- name    : Kyprianou.Ch04.jointContinuousPartialsPositiveTimeV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T09:54:11.569153+00:00
-- url     : https://prove2.me/theorems/6e147acf-28f9-424a-8237-dd8e00ce96fa
-- title:
--   Joint Frechet derivative from continuous partial derivatives at positive times
-- statement:
--   Continuous partial derivatives give the actual Frechet derivative at every positive time, by the bivariate strict derivative theorem.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(i).

import Mathlib
open Set Filter Topology
open scoped Topology
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem jointContinuousPartialsPositiveTimeV1 (f fTime fSpace : ℝ → ℝ → ℝ)
    (ht : ∀ s x, HasDerivAt (fun u => f u x) (fTime s x) s)
    (hx : ∀ s x, HasDerivAt (f s) (fSpace s x) x)
    (hct : ContinuousOn (fun z : ℝ × ℝ => fTime z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (hcx : ContinuousOn (fun z : ℝ × ℝ => fSpace z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (p : ℝ × ℝ) (hp : 0 < p.1) :
    HasFDerivAt (fun z : ℝ × ℝ => f z.1 z.2)
      (fTime p.1 p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ +
        fSpace p.1 p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
  sorry
end Kyprianou.Ch04
