-- Prove2me | Theorems.Thm_MasulloGRH_localComponent_eq_norm_cpow_of_isUnramifiedAt
-- name    : MasulloGRH.localComponent_eq_norm_cpow_of_isUnramifiedAt
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:34:57.043728+00:00
-- url     : https://prove2.me/theorems/86fdee5f-3d38-4c2c-b1ac-ac5cc9a4b89c
-- title:
--   Eqs. (6.3.1.2)–(6.3.1.3) — if $\chi$ is unramified at $v$ then $\chi_v=|\cdot|_v^{it_v}$, $\chi(\mathfrak p_v)=q_v^{-it_v}$, with $t_v$ unique modulo $2\pi/\log q_v$
-- statement:
--   **Unramified local components of a Hecke character are imaginary powers of the absolute value** (equations (6.3.1.2)–(6.3.1.3) of the source).
--
--   Let $F$ be a number field and $\chi$ a Hecke character of $F$, i.e. a continuous homomorphism $C_F=\mathrm{GL}_1(\mathbb A_F)/F^\times\to U(1)$. Let $v$ be a finite place of $F$, $F_v$ the completion, $\mathcal O_{F_v}$ its ring of integers, $q_v=N(\mathfrak p_v)$ the cardinality of the residue field and $|\cdot|_v$ the normalized absolute value, so that $|\pi_v|_v=q_v^{-1}$ for every uniformizer $\pi_v$. Let $\chi_v:F_v^\times\to U(1)$, $\chi_v(x)=\chi(j_v(x))$, be the local component of $\chi$ at $v$ ($j_v$ inserts $x$ at the place $v$ and $1$ elsewhere), and assume that $\chi$ is **unramified** at $v$: $\chi_v(u)=1$ for all $u\in\mathcal O_{F_v}^\times$. Write $\chi(\mathfrak p_v)=\chi_v(\pi_v)$, which does not depend on the uniformizer.
--
--   Then there is a real number $t_v$ such that:
--
--   1. $\chi_v(x)=|x|_v^{it_v}$ for every $x\in F_v^\times$; equivalently $\chi_v|\cdot|_v^s=|\cdot|_v^{s+it_v}$ for every $s\in\mathbb C$;
--   2. $\chi(\mathfrak p_v)=q_v^{-it_v}$;
--   3. a real number $t'$ satisfies $\chi_v=|\cdot|_v^{it'}$ on $F_v^\times$ if and only if
--   $$t'\in t_v+\frac{2\pi}{\log q_v}\,\mathbb Z .$$
--
--   In particular $t_v$ is unique modulo $(2\pi/\log q_v)\mathbb Z$ and has a unique representative in $[0,2\pi/\log q_v)$, and the Euler factor of the Hecke $L$-function at $v$ is
--   $$\bigl(1-\chi(\mathfrak p_v)\,q_v^{-s}\bigr)^{-1}=\frac1{1-q_v^{-s-it_v}},$$
--   which is (6.3.1.4). The source fixes this $t_v$ throughout Chapter 6 to write the Euler factors of $L(s,\chi)$ and the Euler multipliers $\prod_v(1-q_v^{-s-it_v})$ of its non-primitive converse theorem (Theorem 6.3.2.2).
--
--   **Formalization Note.** $\chi_v$ is `HeckeCharacter.localComponent`, "unramified at $v$" is `HeckeCharacter.IsUnramifiedAt`, and $\chi(\mathfrak p_v)$ is `HeckeCharacter.primeValue` (the value at a chosen uniformizer; it is $0$ at ramified places), all from the platform definition `MasulloGRH_HeckeLFunction`. $|x|_v$ is the norm of Mathlib's normed field `v.adicCompletion F`, which is normalized by $|\pi_v|=q_v^{-1}$; powers $|x|_v^{it}$ are complex powers of a positive real number. The source's formula (6.3.1.3), $t_v=i\log\chi_v(\pi_v)/\log q_v$, depends on the branch of the logarithm; it is encoded by items 2 and 3.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 303, §6.3.1, eqs. (6.3.1.2)–(6.3.1.3) and (6.3.1.4)

import Mathlib
import Definitions.Def_MasulloGRH_HeckeLFunction
import Definitions.Def_MasulloGRH_SLocalTamagawaMeasures

open MeasureTheory NumberField IsDedekindDomain

set_option autoImplicit false

namespace MasulloGRH

theorem localComponent_eq_norm_cpow_of_isUnramifiedAt
    (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (hχ : χ.IsUnramifiedAt v) :
    ∃ t : ℝ,
      (∀ x : (v.adicCompletion F)ˣ,
        χ.localComponent v x = ((‖(x : v.adicCompletion F)‖ : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I)) ∧
      χ.primeValue v = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-((t : ℂ) * Complex.I)) ∧
      ∀ t' : ℝ,
        (∀ x : (v.adicCompletion F)ˣ,
          χ.localComponent v x = ((‖(x : v.adicCompletion F)‖ : ℝ) : ℂ) ^ ((t' : ℂ) * Complex.I)) ↔
        ∃ k : ℤ, t' = t + 2 * Real.pi * k / Real.log (Ideal.absNorm v.asIdeal : ℝ) := by sorry

end MasulloGRH
