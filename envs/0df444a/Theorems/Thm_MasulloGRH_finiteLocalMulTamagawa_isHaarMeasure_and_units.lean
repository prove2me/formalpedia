-- Prove2me | Theorems.Thm_MasulloGRH_finiteLocalMulTamagawa_isHaarMeasure_and_units
-- name    : MasulloGRH.finiteLocalMulTamagawa_isHaarMeasure_and_units
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:50:49.543801+00:00
-- url     : https://prove2.me/theorems/2f65d1e9-6552-482a-9680-1c8c452710f3
-- title:
--   Lemma A.3.2.3 — $\mu_v=\frac{q_v}{q_v-1}\,\frac{\nu_v}{|\cdot|_v}$ is the Haar measure on $F_v^\times$ with $\mu_v(\mathcal O_{F_v}^\times)=N(\mathfrak d_v)^{-1/2}$
-- statement:
--   **The local multiplicative Tamagawa measure at a finite place** (Definition A.3.2.2(2) and Lemma A.3.2.3, eqs. (A.3.2.2)–(A.3.2.4) of the source).
--
--   Let $F$ be a number field and $v$ a finite place of $F$ above the prime $p$, with completion $F_v$, ring of integers $\mathcal O_{F_v}$, residue field of cardinality $q_v=N(\mathfrak p_v)$, and normalized absolute value $|\cdot|_v$ ($|\pi_v|_v=q_v^{-1}$ for a uniformizer $\pi_v$). Let $\nu_v$ be the local additive Tamagawa measure on $F_v$ (Definition A.3.1.2(3)): the Haar measure with
--   $$\nu_v(\mathcal O_{F_v})=N(\mathfrak d_v)^{-1/2},\qquad N(\mathfrak d_v)=q_v^{d_v},$$
--   where $\mathfrak d_v=\mathfrak d_{F_v/\mathbb Q_p}$ is the local different and $d_v$ is the exponent of $\mathfrak p_v$ in the different of $F/\mathbb Q$.
--
--   Let $\mu_v$ be the measure on $F_v^\times$ given by
--   $$\mu_v(B)=\frac{q_v}{q_v-1}\int_B\frac{d\nu_v(x)}{|x|_v}\qquad(B\subset F_v^\times\ \text{Borel})$$
--   (`MasulloGRH.finiteLocalMulTamagawa`). Then:
--
--   1. $\mu_v$ is a Haar measure on the multiplicative group $F_v^\times$;
--   2. $\mu_v(\mathcal O_{F_v}^\times)=N(\mathfrak d_v)^{-1/2}=\nu_v(\mathcal O_{F_v})$.
--
--   Hence $\mu_v$ is the **local multiplicative Tamagawa measure** of Definition A.3.2.2(2), the unique Haar measure on $F_v^\times$ with the normalization (A.3.2.2), and the formula $\mu_v=\frac{q_v}{q_v-1}\frac{\nu_v}{|\cdot|_v}$ is (A.3.2.3). In particular $\mu_v(\mathcal O_{F_v}^\times)=1$ for all places $v$ unramified over $\mathbb Q$, which makes the restricted product $\mu=\bigotimes_v\mu_v$ on the idele group meaningful (Lemma A.3.2.4).
--
--   **Formalization Note.** $F_v^\times$ is the unit group of `v.adicCompletion F` with its Borel $\sigma$-algebra, and $\mathcal O_{F_v}^\times$ is the set of units $u$ with `Valued.v u = 1`. $N(\mathfrak d_v)$ is `Ideal.absNorm v.asIdeal ^ multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))`, as in the platform theorem `RiemannMasullo.finiteLocalAdditiveTamagawaMeasure_integers`. The source defines $\mu_v$ by (A.3.2.2) and proves (A.3.2.3); here $\mu_v$ is defined by (A.3.2.3) and the statement is that it is a Haar measure satisfying (A.3.2.2), which is equivalent by uniqueness of Haar measure.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 560, Definition A.3.2.2(2), eq. (A.3.2.2), and Lemma A.3.2.3, eqs. (A.3.2.3)–(A.3.2.4)

import Mathlib
import Definitions.Def_MasulloGRH_SLocalTamagawaMeasures

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal

set_option autoImplicit false

namespace MasulloGRH

theorem finiteLocalMulTamagawa_isHaarMeasure_and_units
    (F : Type*) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    (finiteLocalMulTamagawa F v).IsHaarMeasure ∧
    finiteLocalMulTamagawa F v {u | Valued.v (u : v.adicCompletion F) = 1} =
      (ENNReal.ofReal (Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
        multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)))))⁻¹ := by sorry

end MasulloGRH
