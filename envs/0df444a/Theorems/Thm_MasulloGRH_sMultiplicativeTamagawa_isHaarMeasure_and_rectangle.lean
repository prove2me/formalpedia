-- Prove2me | Theorems.Thm_MasulloGRH_sMultiplicativeTamagawa_isHaarMeasure_and_rectangle
-- name    : MasulloGRH.sMultiplicativeTamagawa_isHaarMeasure_and_rectangle
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:51:02.418896+00:00
-- url     : https://prove2.me/theorems/47a1387e-0891-4fc7-96a4-f592901a426c
-- title:
--   Definition A.3.4.1(2) — $\mu_S$ is a Haar measure on $\mathrm{GL}_1(\mathbb A_{F,S})$ and is the product of the local measures: $\mu_S(\prod_{v\in S}B_v)=\prod_{v\in S}\mu_v(B_v)$
-- statement:
--   **The $S$-local multiplicative Tamagawa measure is the product of the local ones** (Definition A.3.4.1(2), eq. (A.3.4.2) of the source).
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
--   The **local multiplicative Tamagawa measures** (Definition A.3.2.2, Lemma A.3.2.3) are the Haar measures
--   $$\mu_w=\frac{\nu_w}{|\cdot|_w}\ \ \text{on }F_w^\times\ (w\mid\infty),\qquad \mu_v=\frac{q_v}{q_v-1}\,\frac{\nu_v}{|\cdot|_v}\ \ \text{on }F_v^\times\ (v\ \text{finite}),$$
--   and the **$S$-local multiplicative Tamagawa measure** $\mu_S$ on $\mathrm{GL}_1(\mathbb A_{F,S})$ is given, in terms of the $S$-local additive Tamagawa measure $\nu_S=\bigotimes_{v\in S}\nu_v$, by
--   $$d\mu_S(g)=\Big(\prod_{v\in S_f}\frac{q_v}{q_v-1}\Big)\frac{d\nu_S(g)}{|g|_{F,S}}$$
--   (`MasulloGRH.infiniteLocalMulTamagawa`, `MasulloGRH.finiteLocalMulTamagawa`, `MasulloGRH.sMultiplicativeTamagawa`). Then:
--
--   1. $\mu_S$ is a Haar measure on the group $\mathrm{GL}_1(\mathbb A_{F,S})$;
--   2. $\mu_S=\bigotimes_{v\in S}\mu_v$: for all Borel sets $B_v\subset F_v^\times$, $v\in S$,
--   $$\mu_S\Big(\prod_{v\in S}B_v\Big)=\prod_{v\in S}\mu_v(B_v).$$
--
--   This is (A.3.4.2). Together with $\mu_v(\mathcal O_{F_v}^\times)=N(\mathfrak d_v)^{-1/2}$ it gives the measures of the standard compact open subgroups, and $\mu_S$ is the measure against which the $S$-local zeta integrals $\int_{\mathrm{GL}_1(\mathbb A_{F,S})}f(g)\,c(g)\,d\mu_S(g)$ are formed.
--
--   **Formalization Note.** $S$ is represented by the finite set `Sf` of its finite places; the family $(B_v)_{v\in S}$ is a family `A` indexed by the infinite places and a family `B` indexed by `Sf`, and $\prod_vB_v$ is the set of $S$-ideles $g$ whose coordinate at each place is (the value of) an element of the corresponding set. Unit groups carry their Borel $\sigma$-algebras. The right-hand side is a product in $[0,\infty]$ (with $0\cdot\infty=0$). `IsHaarMeasure` is Mathlib's notion: left-invariant, finite on compacts, positive on non-empty open sets.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 561, Definition A.3.4.1(2), eq. (A.3.4.2); p. 560, Definition A.3.2.2 and Lemma A.3.2.3

import Mathlib
import Definitions.Def_MasulloGRH_SLocalTamagawaMeasures

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal

set_option autoImplicit false

namespace MasulloGRH

theorem sMultiplicativeTamagawa_isHaarMeasure_and_rectangle
    (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    (sMultiplicativeTamagawa F Sf).IsHaarMeasure ∧
    ∀ (A : (w : InfinitePlace F) → Set w.Completionˣ)
      (B : (v : Sf) → Set ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)ˣ),
      (∀ w, MeasurableSet (A w)) → (∀ v, MeasurableSet (B v)) →
      sMultiplicativeTamagawa F Sf
          {g | (∀ w : InfinitePlace F, ∃ a ∈ A w, (a : w.Completion) = (g : SAdeleRing F Sf).1 w) ∧
            ∀ v : Sf, ∃ b ∈ B v,
              (b : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) = (g : SAdeleRing F Sf).2 v} =
        (∏ w : InfinitePlace F, infiniteLocalMulTamagawa F w (A w)) *
          ∏ v : Sf, finiteLocalMulTamagawa F (v : HeightOneSpectrum (𝓞 F)) (B v) := by sorry

end MasulloGRH
