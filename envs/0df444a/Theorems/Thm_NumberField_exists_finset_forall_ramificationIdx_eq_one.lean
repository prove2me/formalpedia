-- Prove2me | Theorems.Thm_NumberField_exists_finset_forall_ramificationIdx_eq_one
-- name    : NumberField.exists_finset_forall_ramificationIdx_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/582c4273-ab16-547e-ba95-3942f8a8c101
-- title:
--   Finite extensions of number fields are unramified outside a finite set
-- statement:
--   Let $E$ and $K$ be number fields (fields of characteristic zero, finite-dimensional over $\mathbb{Q}$, living in `Type`) together with an algebra structure of $E$ on $K$, so that $K$ is an extension of $E$. The assertion is that there is a finite set $S_0$ of height-one primes of the ring of integers $\mathcal{O}_E$ with the following property: for every height-one prime $w$ of $\mathcal{O}_K$ such that the prime $w \cap \mathcal{O}_E$ of $\mathcal{O}_E$ lying under $w$ (in Lean, `w.under (𝓞 E)`) does not belong to $S_0$, the ramification index `Ideal.ramificationIdx'` of the prime ideal of $w \cap \mathcal{O}_E$ in the prime ideal of $w$ equals $1$. No Galois, normality or separability hypothesis on $K/E$ is imposed beyond what the number-field assumptions give, and the finite exceptional set is a set of primes of the base field $E$, the condition on $w$ being a condition on the prime of $E$ below it. Note that the ramification index used is the variant `ramificationIdx'`, which agrees with `Ideal.ramificationIdx` for a nonzero prime below.
--
--   This is the standard fact that only finitely many primes of the base field ramify in a finite extension of number fields, packaged in precisely the form needed as an "unramified outside $S$" hypothesis: the exceptional set is a `Finset` of finite places of $E$, which may then be absorbed into any larger set $S$. It is used to discharge such hypotheses in the semilocal analysis of idèle cohomology, in estimates for orbital integrals and restricted-product constructions for automorphic forms, and in the proof that only finitely many places are bad in the cubic-induction step of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_finset_forall_ramificationIdx_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem NumberField.exists_finset_forall_ramificationIdx_eq_one (E K : Type) [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K] :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 E)),
      ∀ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 E) ∉ S₀ → (w.under (𝓞 E)).asIdeal.ramificationIdx' w.asIdeal = 1 := by sorry
