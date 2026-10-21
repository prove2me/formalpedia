-- Prove2me | Theorems.Thm_InterimRatImpl_Sufficiency_step_2
-- name    : InterimRatImpl.Sufficiency.step_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:10:23.042953+00:00
-- url     : https://prove2.me/theorems/b1898722-89ba-49fd-84dc-a2da5d78bf33
-- title:
--   Step 2 — the rationalizable-report deception is acceptable
-- statement:
--   For each type $t_i$, let $\beta_i(t_i)$ contain $t_i$ and every self-report appearing in a rationalizable message of that type. The resulting deception is acceptable for $\hat f$:
--
--   $$
--   \beta_i(t_i)=\{t_i\}\cup\{t_i':\exists m_i\in S_i^\Gamma(T)(t_i),\ m_i^1[i]=t_i'\},
--   \qquad \neg\operatorname{Unacceptable}(\hat f,\beta).
--   $$
--
--   This identifies the outcome-preserving restriction on rationalizable type reports.
--
--   **Formalization Note** The canonical proof uses at least two agents, and the responsive relation throughout this step is the one induced by $\hat f$.
-- source:
--   Kunimoto, Saran & Serrano, Interim Rationalizable Implementation of Functions, Bravo Working Paper # 2020-023 (Brown University, version of October 2020), p. 24 (PDF 25), Step 2; proof pp. 24–26 (PDF 25–27)

import Definitions.Def_InterimRatImpl_Sufficiency_Canonical

namespace InterimRatImpl.Sufficiency

universe u v w
variable {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]
  {T : I → Type v} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
  [∀ i, Nonempty (T i)] {A : Type w} [Fintype A] [DecidableEq A]

/-- Step 2 of Theorem 6.3: the deception induced by rationalizable
self-reports is acceptable. -/
theorem step_2 (E : Env I T A) (fhat : SCF T A)
    (P : CanonParams E fhat) (hcard : 2 ≤ Fintype.card I)
    (hIRM : WeakIRM E fhat) (hNWR : WeakNWR E fhat) :
    ¬ Unacceptable fhat (canonDeception E fhat P) := by sorry

end InterimRatImpl.Sufficiency
