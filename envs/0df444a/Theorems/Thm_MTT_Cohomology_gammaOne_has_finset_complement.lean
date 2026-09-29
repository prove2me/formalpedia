-- Prove2me | Theorems.Thm_MTT_Cohomology_gammaOne_has_finset_complement
-- name    : MTT.Cohomology.gammaOne_has_finset_complement
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-08T06:17:27.95056+00:00
-- url     : https://prove2.me/theorems/ac4dee83-611f-4f92-93b0-904f8eb5d376
-- title:
--   Finite right-coset representatives for $\Gamma_1(N)$
-- statement:
--   Let $N>0$. There is a finite set $R\subseteq \mathrm{SL}_2(\mathbb Z)$ containing exactly one representative of every right coset of $\Gamma_1(N)$: multiplication induces a bijection
--
--   $$
--   \Gamma_1(N)\times R\;\longrightarrow\;\mathrm{SL}_2(\mathbb Z).
--   $$
--
--   This is the finite-coset interface used to express integrals over $\Gamma_1(N)\backslash\mathfrak H$ as finite sums over translates of the standard modular fundamental domain.
--
--   **Formalization Note** The uniqueness and coverage conditions are packaged by Mathlib's `Subgroup.IsComplement`.
-- source:
--   Classical finite-index property of congruence subgroups; Columbia Spring 2021 modular-forms seminar notes, Week 4–5, §1.2, proof of Theorem 1, pp. 7–10, https://www.math.columbia.edu/~dmarcil/Seminars/2021_Spring/Notes/Week4-5.pdf.

import Definitions.Def_MTT_PeriodPairing

set_option autoImplicit false
noncomputable section
open scoped MatrixGroups

theorem MTT.Cohomology.gammaOne_has_finset_complement
    {N : ℕ} (hN : 0 < N) :
    ∃ R : Finset (Matrix.SpecialLinearGroup (Fin 2) ℤ),
      Subgroup.IsComplement
        (CongruenceSubgroup.Gamma1 N : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
        (R : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)) := by sorry
