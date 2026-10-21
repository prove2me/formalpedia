-- Prove2me | Theorems.Thm_InterimRatImpl_Sufficiency_countable_messages
-- name    : InterimRatImpl.Sufficiency.countable_messages
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:10:21.105624+00:00
-- url     : https://prove2.me/theorems/08736765-80d9-47b2-a118-0ee6ba31d45c
-- title:
--   Proof of Theorem 6.3 — canonical message spaces are countable
-- statement:
--   For each agent $i$, the canonical message space $M_i$ is countable:
--
--   $$
--   \forall i\in I,\quad |M_i|\le\aleph_0.
--   $$
--
--   The message records a finite type profile, a positive integer, a challenge for every type in a finite type set, and a pure outcome. This establishes that the mechanism belongs to the class permitted by Definition 3.1.
-- source:
--   Kunimoto, Saran & Serrano, Interim Rationalizable Implementation of Functions, Bravo Working Paper # 2020-023 (Brown University, version of October 2020), p. 20 (PDF 21), sentence after the four message components

import Definitions.Def_InterimRatImpl_Sufficiency_Canonical

namespace InterimRatImpl.Sufficiency

universe u v w
variable {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]
  {T : I → Type v} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
  [∀ i, Nonempty (T i)] {A : Type w} [Fintype A] [DecidableEq A]

/-- p. 20: each canonical message space is countable. -/
theorem countable_messages (E : Env I T A) (fhat : SCF T A)
    (Dstar : DenseLotteries A) :
    ∀ i, Countable (CanonMsg E fhat Dstar i) := by sorry

end InterimRatImpl.Sufficiency
