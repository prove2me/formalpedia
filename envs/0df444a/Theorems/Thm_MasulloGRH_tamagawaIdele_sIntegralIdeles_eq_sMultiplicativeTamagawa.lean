-- Prove2me | Theorems.Thm_MasulloGRH_tamagawaIdele_sIntegralIdeles_eq_sMultiplicativeTamagawa
-- name    : MasulloGRH.tamagawaIdele_sIntegralIdeles_eq_sMultiplicativeTamagawa
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:50:53.629815+00:00
-- url     : https://prove2.me/theorems/1106229d-1574-416f-a856-640e9628427b
-- title:
--   Lemma A.3.2.4 — the idelic Tamagawa measure is a restricted product: $\mu=\mu_S\otimes\bigotimes_{v\notin S}\mu_v$ on $\mathrm{GL}_1(\mathbb A_{F,S})\times\prod_{v\notin S}\mathcal O_{F_v}^\times$
-- statement:
--   **The Tamagawa measure of the idele group is the restricted product of the local multiplicative Tamagawa measures** (Lemma A.3.2.4, eq. (A.3.2.5) of the source).
--
--   Let $F$ be a number field. For a place $v$ of $F$ let $F_v$ be the completion of $F$ at $v$ and $|\cdot|_v$ the normalized absolute value on $F_v$: the usual absolute value if $F_v\simeq\mathbb R$, its square if $F_v\simeq\mathbb C$, and the absolute value with $|\pi_v|_v=q_v^{-1}$ if $v$ is finite, where $\pi_v$ is a uniformizer of the ring of integers $\mathcal O_{F_v}$ and $q_v=N(\mathfrak p_v)$ is the cardinality of the residue field. The **local additive Tamagawa measure** $\nu_v$ on $F_v$ (Definition A.3.1.2 of the source) is: Lebesgue measure $dx$ if $F_v\simeq\mathbb R$; the measure $|dz\wedge d\bar z|=2\,dx\,dy$ if $F_v\simeq\mathbb C$; and, if $v$ is a finite place above the prime $p$, the Haar measure on $F_v$ with
--   $$\nu_v(\mathcal O_{F_v})=N(\mathfrak d_v)^{-1/2},\qquad N(\mathfrak d_v)=q_v^{d_v},$$
--   where $\mathfrak d_v=\mathfrak d_{F_v/\mathbb Q_p}$ is the local different and $d_v$ is the exponent of the prime $\mathfrak p_v$ in the different $\mathfrak d_{F/\mathbb Q}$ of $F$ (so $d_v=0$ unless $v$ is ramified over $\mathbb Q$, and $\prod_vN(\mathfrak d_v)=|d_F|$ is the absolute value of the discriminant of $F$).
--
--   The **local multiplicative Tamagawa measures** (Definition A.3.2.2, Lemma A.3.2.3) are the Haar measures $\mu_w=\nu_w/|\cdot|_w$ on $F_w^\times$ for $w\mid\infty$ and $\mu_v=\frac{q_v}{q_v-1}\,\nu_v/|\cdot|_v$ on $F_v^\times$ for $v$ finite, so that $\mu_v(\mathcal O_{F_v}^\times)=N(\mathfrak d_v)^{-1/2}$.
--
--   Let $\mathrm{GL}_1(\mathbb A_F)$ be the idele group, $|\cdot|_F$ the idelic norm, $C_F=\mathrm{GL}_1(\mathbb A_F)/F^\times$ the idele class group and $C_F^1$ the subgroup of classes of norm $1$. The **Tamagawa measure** $\mu$ on $\mathrm{GL}_1(\mathbb A_F)$ (Definition A.3.2.1; `MasulloGRH.tamagawaIdele`) is the Haar measure such that the measure $\bar\mu$ induced on $C_F$ by $\mu$ and the counting measure on $F^\times$, together with $dt/t$ on $\mathbb R_{>0}\simeq C_F/C_F^1$, gives $C_F^1$ the volume
--   $$\bar\mu_1(C_F^1)=\frac{2^{r_1}(2\pi)^{r_2}h_FR_F}{|d_F|^{1/2}w_F},$$
--   with $r_1$, $r_2$ the numbers of real and complex places, $h_F$ the class number, $R_F$ the regulator, $d_F$ the discriminant and $w_F$ the number of roots of unity of $F$.
--
--   Let $S$ be a finite set of places of $F$ containing all archimedean places, $S_f$ the set of its finite places, $\mathrm{GL}_1(\mathbb A_{F,S})=\prod_{v\in S}F_v^\times$, and $\mu_S=\bigotimes_{v\in S}\mu_v$ the $S$-local multiplicative Tamagawa measure (Definition A.3.4.1(2); `MasulloGRH.sMultiplicativeTamagawa`). Then $\mu=\bigotimes_v\mu_v$ in the sense of restricted products: the restriction of $\mu$ to the open subgroup $\mathrm{GL}_1(\mathbb A_{F,S})\times\prod_{v\notin S}\mathcal O_{F_v}^\times$ is $\mu_S\otimes\bigotimes_{v\notin S}\mu_v$. Explicitly, for every Borel set $B\subset\mathrm{GL}_1(\mathbb A_{F,S})$,
--   $$\mu\Big(B\times\prod_{v\notin S}\mathcal O_{F_v}^\times\Big)=\mu_S(B)\cdot\prod_{v\notin S}N(\mathfrak d_v)^{-1/2}=\mu_S(B)\cdot|d_F|^{-1/2}\prod_{v\in S_f}N(\mathfrak d_v)^{1/2}.$$
--
--   Since every idele is a unit outside some finite $S$, these identities determine $\mu$. In view of the normalization of $\mu$, the statement is equivalent to Tate's computation of the volume of the compact group $C_F^1$ for the product measure $\bigotimes_v\mu_v$ — the form of the analytic class number formula that produces the residue of the completed zeta function in the global zeta integrals of Chapter 3.
--
--   **Formalization Note.** $S$ is represented by the finite set `Sf` of its finite places. The set $B\times\prod_{v\notin S}\mathcal O_{F_v}^\times$ is the set of ideles $g$ that are units at all finite places outside $S$ (`MasulloGRH.sIntegralIdeles Sf`) and whose family of coordinates at the places of $S$ is (the value of) an element of $B$. The infinite product is written in the second form, with $|d_F|$ = `|discr F|` and $N(\mathfrak d_v)$ = `Ideal.absNorm v.asIdeal ^ multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))`. In `MasulloGRH.tamagawaIdele` the volume (A.3.2.1) is Mathlib's `dedekindZeta_residue F`, which is defined by that formula. The idele group and $\mathrm{GL}_1(\mathbb A_{F,S})$ carry their Borel $\sigma$-algebras.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 560, Lemma A.3.2.4, eq. (A.3.2.5), with Definition A.3.2.1 and eq. (A.3.2.1), pp. 559–560, and Definition A.3.2.2, p. 560; classical reference (cited after the lemma): D. Ramakrishnan, R.J. Valenza, Fourier Analysis on Number Fields, Springer, Thm. 7.21

import Mathlib
import Definitions.Def_MasulloGRH_ZetaIntegrals
import Definitions.Def_MasulloGRH_SLocalTamagawaMeasures

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal

set_option autoImplicit false

namespace MasulloGRH

theorem tamagawaIdele_sIntegralIdeles_eq_sMultiplicativeTamagawa
    (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (B : Set (SIdeleGroup F Sf)) (hB : MeasurableSet B) :
    tamagawaIdele F
        {g : IdeleGroup F | g ∈ sIntegralIdeles Sf ∧
          ∃ b ∈ B, (b : SAdeleRing F Sf) =
            ((g : AdeleRing (𝓞 F) F).1,
              fun v : Sf => (g : AdeleRing (𝓞 F) F).2 (v : HeightOneSpectrum (𝓞 F)))} =
      sMultiplicativeTamagawa F Sf B *
        ((ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|))⁻¹ *
          ∏ v ∈ Sf, ENNReal.ofReal (Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
            multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))))) := by sorry

end MasulloGRH
