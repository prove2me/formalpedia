-- Prove2me | Theorems.Thm_InterimRatImpl_Sufficiency_uniqueness
-- name    : InterimRatImpl.Sufficiency.uniqueness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:10:30.959867+00:00
-- url     : https://prove2.me/theorems/bd0d6f6c-31d2-4c81-9143-b8206c27a592
-- title:
--   Proof of Theorem 6.3 — Steps 1 and 2 give uniqueness
-- statement:
--   For every type profile $t$ and every message profile $m$ rationalizable at $t$, the canonical mechanism selects exactly $\hat f(t)$:
--
--   $$
--   m\in S^\Gamma(T)(t)\quad\Longrightarrow\quad g(m)=\hat f(t).
--   $$
--
--   The conclusion ranges over every state, including states outside the designer's target set $T^*$.
-- source:
--   Kunimoto, Saran & Serrano, Interim Rationalizable Implementation of Functions, Bravo Working Paper # 2020-023 (Brown University, version of October 2020), p. 26 (PDF 27), sentence following Step 2

import Definitions.Def_InterimRatImpl_Sufficiency_Canonical

namespace InterimRatImpl.Sufficiency

universe u v w
variable {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]
  {T : I → Type v} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
  [∀ i, Nonempty (T i)] {A : Type w} [Fintype A] [DecidableEq A]

/-- The conclusion drawn from Steps 1 and 2 on p. 26. -/
theorem uniqueness (E : Env I T A) (fhat : SCF T A)
    (P : CanonParams E fhat) (hcard : 2 ≤ Fintype.card I)
    (hIRM : WeakIRM E fhat) (hNWR : WeakNWR E fhat) :
    ∀ t m, (∀ i, m i ∈ SGamma E (canonG E fhat P) i (t i)) →
      canonG E fhat P m = fhat t := by sorry

end InterimRatImpl.Sufficiency
