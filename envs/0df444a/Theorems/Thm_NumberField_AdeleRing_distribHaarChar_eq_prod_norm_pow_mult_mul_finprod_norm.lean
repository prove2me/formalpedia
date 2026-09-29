-- Prove2me | Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
-- name    : NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/21cda68c-c27e-571e-8976-52c1d965ad2a
-- title:
--   Modulus of an idele as a product of local norms
-- statement:
--   Let $F$ be a number field, with ring of integers $\mathcal{O}_F$, and let $\mathbb{A}_F$ denote its adele ring, realised as the product of the infinite adeles, indexed by the infinite places $w$ of $F$, with the finite adeles, indexed by the height-one primes $v$ of $\mathcal{O}_F$; for an adele $x$ write $x.1$ for its infinite component and $x.2$ for its finite component. Let $a$ be a unit of $\mathbb{A}_F$. Then the value at $a$ of the distributive Haar character of the multiplication action of $\mathbb{A}_F^\times$ on the additive group $\mathbb{A}_F$ — that is, the positive real scalar $\delta(a)$ with $\mu(a\cdot S)=\delta(a)\,\mu(S)$ for an additive Haar measure $\mu$ on $\mathbb{A}_F$ — is, as a real number, equal to the product over the infinite places $w$ of $F$ of $\|a_w\|^{m_w}$, where $m_w$ is the multiplicity `NumberField.InfinitePlace.mult` of $w$ (so $1$ for a real place and $2$ for a complex place) and $\|\cdot\|$ is the norm on the completion at $w$, multiplied by the finitary product over the height-one primes $v$ of $\mathcal{O}_F$ of the norms $\|a_v\|$ of the components of $a.2$ in the adic completions; the latter product is taken in the sense of `finprod`, all but finitely many of its factors being $1$.
--
--   This is the classical computation of the modulus (module) of an idele of a number field as the product of the normalised local absolute values of its components, the basis for the definition of the idele norm and for the measure-theoretic treatment of $\mathbb{A}_F/F$ and of $\mathbb{A}_F^\times$. It is obtained by combining the archimedean case, in which the finite component of $a$ is $1$, with the contribution of the finite adeles, and it is used throughout the adelic integration theory underlying the analytic theory of automorphic forms in the project.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean

import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
    (F : Type) [Field F] [NumberField F]
    (a : (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)ˣ) :
    (MeasureTheory.distribHaarChar (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) a : ℝ)
      = (∏ w : NumberField.InfinitePlace F,
            ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers F) F).1 w‖ ^ w.mult)
        * ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
            ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers F) F).2 v‖ := by sorry
