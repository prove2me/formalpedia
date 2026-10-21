-- Prove2me | Theorems.Thm_InterimRatImpl_Sufficiency_lemma_6_2_a
-- name    : InterimRatImpl.Sufficiency.lemma_6_2_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:10:21.029009+00:00
-- url     : https://prove2.me/theorems/b5f82a12-9490-46db-8639-f6416b7fe1d9
-- title:
--   Lemma 6.2(a) (in the form used in Step 1 of Theorem 6.3) — a challenge beating the full-support mixture
-- statement:
--   Assume $f$ satisfies weak NWR. Fix an agent $i$, true type $t_i$, announced type $\tilde t_i$, and a distribution $\phi_i$ on pairs of other-agent type profiles. There is a challenge $y\in Y_i^*[\tilde t_i,f]$ whose expected utility to the true type strictly exceeds the full-support mixture $y_i^{\tilde t_i,f}$:
--
--   $$
--   \sum_{s,s'}\phi_i(s,s')u_i(y(s'),(t_i,s))>
--   \sum_{s,s'}\phi_i(s,s')u_i(y_i^{\tilde t_i,f}(s'),(t_i,s)).
--   $$
--
--   The printed lemma is the specialization $\tilde t_i=t_i$. Step 1 uses the displayed cross-type form.
--
--   **Formalization Note** $\Delta^*(A)$ is countable and dense, and the mixture assigns positive normalized weight to every member of $Y_i^*[\tilde t_i,f]$.
-- source:
--   Kunimoto, Saran & Serrano, Interim Rationalizable Implementation of Functions, Bravo Working Paper # 2020-023 (Brown University, version of October 2020), p. 19 (PDF 20), Lemma 6.2(a); cross-type form used in Step 1, p. 23 (PDF 24)

import Definitions.Def_InterimRatImpl_Sufficiency_Canonical

namespace InterimRatImpl.Sufficiency

universe u v w
variable {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]
  {T : I → Type v} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
  [∀ i, Nonempty (T i)] {A : Type w} [Fintype A] [DecidableEq A]

/-- Lemma 6.2(a), p. 19, in the cross-type form invoked on p. 23. -/
theorem lemma_6_2_a (E : Env I T A) (f : SCF T A) (hNWR : WeakNWR E f)
    (Dstar : DenseLotteries A) (ybar : ∀ i, T i → Others T i → Lottery A)
    (hybar : FullSupportYbar Dstar E f ybar)
    (i : I) (ti ttilde : T i)
    (φ : {p : Others T i × Others T i → ℝ //
      p ∈ stdSimplex ℝ (Others T i × Others T i)}) :
    ∃ y ∈ Ystar Dstar E i ttilde f,
      (∑ p, φ.1 p * eu E i (y p.2) (join i ti p.1)) >
      (∑ p, φ.1 p * eu E i (ybar i ttilde p.2) (join i ti p.1)) := by sorry

end InterimRatImpl.Sufficiency
