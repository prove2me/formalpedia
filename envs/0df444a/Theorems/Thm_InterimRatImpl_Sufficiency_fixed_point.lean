-- Prove2me | Theorems.Thm_InterimRatImpl_Sufficiency_fixed_point
-- name    : InterimRatImpl.Sufficiency.fixed_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:09:21.451596+00:00
-- url     : https://prove2.me/theorems/3d73973a-55e0-442c-96a4-094225e777ce
-- title:
--   §3 — best-response operator and greatest fixed point
-- statement:
--   For every mechanism $\Gamma$, the best-response operator $b$ on message correspondences is monotone. Its greatest post-fixed point $S^\Gamma(T)$ is a fixed point, and every post-fixed correspondence lies below it:
--
--   $$
--   S\le b(S)\quad\Longrightarrow\quad S\le S^\Gamma(T),\qquad b(S^\Gamma(T))=S^\Gamma(T).
--   $$
--
--   These facts justify deriving rationalizability from a correspondence whose messages remain best responses.
-- source:
--   Kunimoto, Saran & Serrano, Interim Rationalizable Implementation of Functions, Bravo Working Paper # 2020-023 (Brown University, version of October 2020), p. 5 (PDF 6), paragraph following the definition of b

import Definitions.Def_InterimRatImpl_Sufficiency_Model

namespace InterimRatImpl.Sufficiency

universe u v w x
variable {I : Type u} [Fintype I] [DecidableEq I]
  {T : I → Type v} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
  [∀ i, Nonempty (T i)] {A : Type w} [Fintype A] [DecidableEq A]
  {M : I → Type x}

/-- §3, p. 5: b is increasing, its greatest post-fixed point is fixed,
and every post-fixed point lies below it. -/
theorem fixed_point (E : Env I T A) (g : Profile M → Lottery A) :
    Monotone (b E g) ∧ b E g (SGamma E g) = SGamma E g ∧
    (∀ S : MsgCorr T M, S ≤ b E g S → S ≤ SGamma E g) := by sorry

end InterimRatImpl.Sufficiency
