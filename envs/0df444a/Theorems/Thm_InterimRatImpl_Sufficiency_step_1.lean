-- Prove2me | Theorems.Thm_InterimRatImpl_Sufficiency_step_1
-- name    : InterimRatImpl.Sufficiency.step_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:10:31.61098+00:00
-- url     : https://prove2.me/theorems/63113df8-114a-492a-a502-6ee2001d4a00
-- title:
--   Step 1 — rationalizable messages have level one
-- statement:
--   In the canonical mechanism, every rationalizable message of every type has integer component equal to one:
--
--   $$
--   m_i\in S_i^\Gamma(T)(t_i)\quad\Longrightarrow\quad m_i^2=1.
--   $$
--
--   The result excludes the challenge and pure-outcome branches from rationalizable play.
--
--   **Formalization Note** The canonical construction is used with at least two agents; at one agent, Rule 2-1 does not select a unique type.
-- source:
--   Kunimoto, Saran & Serrano, Interim Rationalizable Implementation of Functions, Bravo Working Paper # 2020-023 (Brown University, version of October 2020), p. 20 (PDF 21), Step 1; proof pp. 20–24 (PDF 21–25)

import Definitions.Def_InterimRatImpl_Sufficiency_Canonical

namespace InterimRatImpl.Sufficiency

universe u v w
variable {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]
  {T : I → Type v} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
  [∀ i, Nonempty (T i)] {A : Type w} [Fintype A] [DecidableEq A]

/-- Step 1 of Theorem 6.3: every rationalizable message has level one. -/
theorem step_1 (E : Env I T A) (fhat : SCF T A)
    (P : CanonParams E fhat) (hcard : 2 ≤ Fintype.card I)
    (hNWR : WeakNWR E fhat) :
    ∀ i ti (mi : CanonMsg E fhat P.Dstar i),
      mi ∈ SGamma E (canonG E fhat P) i ti → mi.level = 1 := by sorry

end InterimRatImpl.Sufficiency
