-- Prove2me | Theorems.Thm_MTT_Eigenform_quadratic_centralValue_ne_zero_iff_of_hasMinimalLevel
-- name    : MTT.Eigenform.quadratic_centralValue_ne_zero_iff_of_hasMinimalLevel
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-10-18T18:44:30.692876+00:00
-- url     : https://prove2.me/theorems/cd1527c7-1674-4b42-a64c-19fa6926a659
-- title:
--   Quadratic central nonvanishing is invariant under passage to minimal level
-- statement:
--   Let $k\geq2$ be even, let $N,M>0$, and fix a complex embedding $\iota$ of the algebraic numbers. Let $f$ and $g$ be normalized cuspidal Hecke eigenforms of weight $k$ and levels $N$ and $M$, respectively, with arbitrary nebentypus. Assume that their prime Hecke eigenvalues and nebentypus values agree outside a finite set of primes, and that $g$ has the least positive level among eigenforms in this Hecke system.
--
--   For every primitive quadratic Dirichlet character $\eta$ whose conductor is coprime to $NM$,
--
--   $$L(f,\eta,k/2)\ne0\quad\Longleftrightarrow\quad L(g,\eta,k/2)\ne0.$$
--
--   Here the central values are the MTT twisted critical values associated with the chosen complex embedding. In the formal statement, their critical index is $k/2-1$, and quadratic means that the character has exact order two.
-- source:
--   Derived from the newform and oldform theory in Kenneth A. Ribet and William A. Stein, Lectures on Modular Forms and Hecke Operators, Theorem 9.1.10, pp. 74–75, and Section 9.2, pp. 76–77, https://wstein.org/books/ribet-stein/main.pdf. The formal proof uses the proved Prove2Me elementary strict Hecke estimate CuspForm.norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen (e8e0b1c5-9141-5ca4-b2fa-f93c3dd0f1dd), the Hecke adjoint relation CuspForm.conj_heckeEigenvalue_eq_of_hasNebentypus (81eee6d3-7504-5d39-9d21-6adcea5f50b0), and the proved ramified bound MTT.Eigenform.norm_coeff_le_of_dvd_of_hasMinimalLevel (c93d8464-4061-4771-81b0-023d05c07bfc). This is a derived nonvanishing transfer result, not a claim of the sharp Ramanujan–Petersson bound.

import Definitions.Def_MTT_HeckeEquivalence
import Definitions.Def_KN_HorizontalPadicL

set_option autoImplicit false

open HorizontalPadicL

theorem MTT.Eigenform.quadratic_centralValue_ne_zero_iff_of_hasMinimalLevel
    {N M k : ℕ} (hN : 0 < N) (hM : 0 < M) (hk : 2 ≤ k) (heven : Even k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) (g : MTT.Eigenform M k ι)
    (hfg : f.SameHeckeSystem g) (hg : g.HasMinimalLevel)
    (η : DirichletCharacterWithLevel) (hη : η.2.IsPrimitive)
    (horder : orderOf η.2 = 2) (hcop : Nat.Coprime (N * M) η.2.conductor) :
    (@MTT.criticalLValue ι f.form η.1.1 ⟨Nat.ne_of_gt η.1.2⟩ η.2 (k / 2 - 1) ≠ 0) ↔
      (@MTT.criticalLValue ι g.form η.1.1 ⟨Nat.ne_of_gt η.1.2⟩ η.2 (k / 2 - 1) ≠ 0) := by sorry
