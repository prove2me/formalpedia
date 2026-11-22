-- Prove2me | Theorems.Thm_MasulloGRH_sAdditiveTamagawa_isAddHaarMeasure
-- name    : MasulloGRH.sAdditiveTamagawa_isAddHaarMeasure
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:50:45.291769+00:00
-- url     : https://prove2.me/theorems/5935d7b9-da13-4c21-8bf6-8b2f90a07bfc
-- title:
--   Definition A.3.4.1(1) — the $S$-local additive Tamagawa measure $\nu_S=\bigotimes_{v\in S}\nu_v$ is a Haar measure on $\mathbb A_{F,S}$
-- statement:
--   **The $S$-local additive Tamagawa measure is a Haar measure** (Definition A.3.4.1(1), eq. (A.3.4.1) of the source).
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
--   The **$S$-local additive Tamagawa measure** is the product measure
--   $$\nu_S=\bigotimes_{v\in S}\nu_v\quad\text{on }\mathbb A_{F,S}=\prod_{v\in S}F_v$$
--   (`MasulloGRH.sAdditiveTamagawa`). Then $\nu_S$ is a Haar measure of the additive group of $\mathbb A_{F,S}$: it is invariant under translations, finite on compact subsets and positive on non-empty open subsets.
--
--   The source introduces $\nu_S$ as "the Haar measure on $\mathbb A_{F,S}$ given by" this product. It is the measure defining the $S$-local Fourier transform and the $L^2$-spaces of $\mathbb A_{F,S}$ in the study of the $S$-local $\theta$-functions.
--
--   **Formalization Note.** $S$ is represented by the finite set `Sf` of its finite places. $\mathbb A_{F,S}$ carries the product of the Borel $\sigma$-algebras of the factors $F_v$, which is its Borel $\sigma$-algebra. `IsAddHaarMeasure` is Mathlib's notion: left-invariant, finite on compacts, positive on non-empty open sets.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 561, Definition A.3.4.1(1), eq. (A.3.4.1)

import Mathlib
import Definitions.Def_MasulloGRH_SLocalTamagawaMeasures

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal

set_option autoImplicit false

namespace MasulloGRH

theorem sAdditiveTamagawa_isAddHaarMeasure
    (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    (sAdditiveTamagawa F Sf).IsAddHaarMeasure := by sorry

end MasulloGRH
