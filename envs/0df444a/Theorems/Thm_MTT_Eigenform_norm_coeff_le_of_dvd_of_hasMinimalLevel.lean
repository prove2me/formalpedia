-- Prove2me | Theorems.Thm_MTT_Eigenform_norm_coeff_le_of_dvd_of_hasMinimalLevel
-- name    : MTT.Eigenform.norm_coeff_le_of_dvd_of_hasMinimalLevel
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-10-18T18:20:40.85241+00:00
-- url     : https://prove2.me/theorems/c93d8464-4061-4771-81b0-023d05c07bfc
-- title:
--   Ramified local parameter bound for a minimal-level eigenform
-- statement:
--   Let $M>0$ and $k\geq2$ be integers, fix an embedding $\iota:\overline{\mathbb Q}\hookrightarrow\mathbb C$, and let $g$ be a normalized cuspidal Hecke eigenform of weight $k$ and level $\Gamma_1(M)$ with algebraic Fourier coefficients and arbitrary nebentypus. Assume that $M$ is the least positive level among eigenforms with the same prime Hecke eigenvalues and nebentypus values outside a finite set of primes. Then, for every prime $q\mid M$,
--
--   $$|\iota(a_q(g))|\leq q^{(k-1)/2}.$$
--
--   This is the ramified case of the local-parameter bound: the local parameter at a prime dividing the level is the coefficient $a_q(g)$. No triviality, reality, or conductor restriction is imposed on the nebentypus.
--
--   **Formalization note.** Minimality is expressed by `MTT.Eigenform.HasMinimalLevel`; the coefficient is `g.coeff q`. The proof first identifies the given normalized eigenform as a primitive form and then applies the established squared coefficient bound for primitive forms.
-- source:
--   Kenneth A. Ribet and William A. Stein, Lectures on Modular Forms and Hecke Operators, Theorem 9.1.10(2), p. 75, https://wstein.org/books/ribet-stein/main.pdf. The bound here is the weaker uniform inequality |a_q|^2 <= q^(k-1) at ramified primes. The passage from least positive level in the Hecke system to a primitive form is proved in the attached formal proof using primitive-form extraction and uniqueness.

import Definitions.Def_MTT_HeckeEquivalence
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

theorem MTT.Eigenform.norm_coeff_le_of_dvd_of_hasMinimalLevel
{M k : ℕ} (hM : 0 < M) (hk : 2 ≤ k) (ι : MTT.Qbar →+* ℂ)
    (g : MTT.Eigenform M k ι) (hg : g.HasMinimalLevel)
    (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) :
    ‖ι (g.coeff q)‖ ≤ (q : ℝ) ^ (((k : ℝ) - 1) / 2) := by sorry
