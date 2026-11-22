-- Prove2me | Theorems.Thm_MasulloGRH_sIntegerLattice_covolume_sAdditiveTamagawa
-- name    : MasulloGRH.sIntegerLattice_covolume_sAdditiveTamagawa
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:50:54.219185+00:00
-- url     : https://prove2.me/theorems/7bcf6c88-1001-49c8-a624-39bcd50a0399
-- title:
--   Remark A.3.4.2 — covolume of the $S$-integers: $\nu_S(\mathbb A_{F,S}/\mathcal O_{F,S})=|d_F|^{1/2}\prod_{v\in S_f}N(\mathfrak d_v)^{-1/2}$
-- statement:
--   **The covolume of the $S$-integers for the $S$-local additive Tamagawa measure** (Remark A.3.4.2 of the source; corrected form of the second equality of (A.3.1.3)).
--
--   Let $F$ be a number field. For a place $v$ of $F$ let $F_v$ be the completion of $F$ at $v$ and $|\cdot|_v$ the normalized absolute value on $F_v$: the usual absolute value if $F_v\simeq\mathbb R$, its square if $F_v\simeq\mathbb C$, and the absolute value with $|\pi_v|_v=q_v^{-1}$ if $v$ is finite, where $\pi_v$ is a uniformizer of the ring of integers $\mathcal O_{F_v}$ and $q_v=N(\mathfrak p_v)$ is the cardinality of the residue field. The **local additive Tamagawa measure** $\nu_v$ on $F_v$ (Definition A.3.1.2 of the source) is: Lebesgue measure $dx$ if $F_v\simeq\mathbb R$; the measure $|dz\wedge d\bar z|=2\,dx\,dy$ if $F_v\simeq\mathbb C$; and, if $v$ is a finite place above the prime $p$, the Haar measure on $F_v$ with
--   $$\nu_v(\mathcal O_{F_v})=N(\mathfrak d_v)^{-1/2},\qquad N(\mathfrak d_v)=q_v^{d_v},$$
--   where $\mathfrak d_v=\mathfrak d_{F_v/\mathbb Q_p}$ is the local different and $d_v$ is the exponent of the prime $\mathfrak p_v$ in the different $\mathfrak d_{F/\mathbb Q}$ of $F$ (so $d_v=0$ unless $v$ is ramified over $\mathbb Q$, and $\prod_vN(\mathfrak d_v)=|d_F|$ is the absolute value of the discriminant of $F$).
--
--   Let $S$ be a finite set of places of $F$ containing all archimedean places and $S_f\subset S$ the set of its finite places. Write
--   $$\mathbb A_{F,S}=\prod_{v\in S}F_v,\qquad \mathrm{GL}_1(\mathbb A_{F,S})=\prod_{v\in S}F_v^\times,\qquad |g|_{F,S}=\prod_{v\in S}|g_v|_v$$
--   for the ring of $S$-adeles (with the product topology), the group of $S$-ideles and the $S$-idelic norm, and
--   $$\mathcal O_{F,S}=\{\xi\in F:\ \xi\in\mathcal O_{F_v}\ \text{for every place }v\notin S\}$$
--   for the ring of $S$-integers, embedded diagonally in $\mathbb A_{F,S}$ as a discrete cocompact subgroup.
--
--   Let $\nu_S=\bigotimes_{v\in S}\nu_v$ be the $S$-local additive Tamagawa measure on $\mathbb A_{F,S}$ (Definition A.3.4.1(1); `MasulloGRH.sAdditiveTamagawa`). Then the volume of the compact quotient $\mathbb A_{F,S}/\mathcal O_{F,S}$, for the measure induced by $\nu_S$ and the counting measure on $\mathcal O_{F,S}$, is the prime-to-$S_f$ part of $|d_F|^{1/2}$: for every fundamental domain $D\subset\mathbb A_{F,S}$ of the translation action of $\mathcal O_{F,S}$,
--   $$\nu_S(D)=|d_F|^{1/2}\prod_{v\in S_f}N(\mathfrak d_v)^{-1/2}=\prod_{v\notin S}N(\mathfrak d_v)^{1/2},$$
--   where $d_F$ is the discriminant of $F$.
--
--   In particular the covolume is $|d_F|^{1/2}$ for $S=S_\infty$ (the classical covolume of $\mathcal O_F$ in $F\otimes_{\mathbb Q}\mathbb R$, with the measure $2\,dx\,dy$ at the complex places), and it equals $1$ exactly when $S$ contains every finite place of $F$ that ramifies over $\mathbb Q$. The covolume is the constant in the $S$-local Poisson summation formula for the lattice $\mathcal O_{F,S}\subset\mathbb A_{F,S}$.
--
--   **Deviation from the source.** Lemma A.3.1.3 asserts $\nu_S=\bigotimes_{v\in S}\nu_v$ for the measure $\nu_S$ of Definition A.3.1.1, normalized by $\nu_S(\mathbb A_{F,S}/\mathcal O_{F,S})=1$; this fails when a ramified place is missing from $S$ (for $F=\mathbb Q(i)$ and $S=S_\infty$ the unit square of $\mathbb C$ has measure $2$ for $2\,dx\,dy$). The correct value of the covolume is the one stated in Remark A.3.4.2, which is formalized here; the last sentence of that remark ("this is $1$ unless $S$ contains all finite places that ramify") has the condition reversed.
--
--   **Formalization Note.** $S$ is represented by the finite set `Sf` of its finite places. "Fundamental domain" is Mathlib's `IsAddFundamentalDomain` for the additive subgroup `MasulloGRH.sIntegerLattice Sf` (the diagonal image of $\mathcal O_{F,S}$) and the measure $\nu_S$; all fundamental domains have the same measure, and the set $D_{F,S}$ of `MasulloGRH.sIntegerFundamentalDomain` is one. $N(\mathfrak d_v)$ is `Ideal.absNorm v.asIdeal ^ multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))`; the value is an element of $[0,\infty]$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 562, Remark A.3.4.2 (last paragraph); see also p. 556, Lemma A.3.1.3 and its proof

import Mathlib
import Definitions.Def_MasulloGRH_SLocalTamagawaMeasures

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal

set_option autoImplicit false

namespace MasulloGRH

theorem sIntegerLattice_covolume_sAdditiveTamagawa
    (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (D : Set (SAdeleRing F Sf))
    (hD : IsAddFundamentalDomain (sIntegerLattice Sf) D (sAdditiveTamagawa F Sf)) :
    sAdditiveTamagawa F Sf D =
      ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|) *
        ∏ v ∈ Sf, (ENNReal.ofReal (Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
          multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)))))⁻¹ := by sorry

end MasulloGRH
