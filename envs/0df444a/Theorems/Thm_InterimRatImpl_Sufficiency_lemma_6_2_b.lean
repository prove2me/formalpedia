-- Prove2me | Theorems.Thm_InterimRatImpl_Sufficiency_lemma_6_2_b
-- name    : InterimRatImpl.Sufficiency.lemma_6_2_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:09:24.923064+00:00
-- url     : https://prove2.me/theorems/202eb104-53b9-4ec3-b8ae-ef75f124b76a
-- title:
--   Lemma 6.2(b) — a pure outcome beats the baseline
-- statement:
--   Assume $f$ satisfies weak NWR and $\bar\alpha$ is a lottery assigning positive weight to every pure outcome. For any agent $i$, type $t_i$, and probability distribution $z_i$ on the other agents' types, some pure outcome $a$ has strictly greater expected utility than $\bar\alpha$:
--
--   $$
--   \sum_s z_i(s)u_i(a,(t_i,s))>
--   \sum_s z_i(s)u_i(\bar\alpha,(t_i,s)).
--   $$
--
--   The comparison supplies the profitable pure-outcome deviation used under Rule 3.
-- source:
--   Kunimoto, Saran & Serrano, Interim Rationalizable Implementation of Functions, Bravo Working Paper # 2020-023 (Brown University, version of October 2020), p. 19 (PDF 20), Lemma 6.2(b)

import Definitions.Def_InterimRatImpl_Sufficiency_Model

namespace InterimRatImpl.Sufficiency

universe u v w
variable {I : Type u} [Fintype I] [DecidableEq I]
  {T : I → Type v} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
  [∀ i, Nonempty (T i)] {A : Type w} [Fintype A] [DecidableEq A]

/-- Lemma 6.2(b), p. 19, for any full-support baseline lottery. -/
theorem lemma_6_2_b (E : Env I T A) (f : SCF T A) (hNWR : WeakNWR E f)
    (abar : Lottery A) (habar : ∀ a, 0 < abar.1 a)
    (i : I) (ti : T i)
    (z : {p : Others T i → ℝ // p ∈ stdSimplex ℝ (Others T i)}) :
    ∃ a : A,
      (∑ s, z.1 s * E.u i a (join i ti s)) >
      (∑ s, z.1 s * eu E i abar (join i ti s)) := by sorry

end InterimRatImpl.Sufficiency
