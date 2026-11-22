-- Prove2me | Theorems.Thm_MasulloGRH_tamagawaAdelic_integralOutside_eq_sAdditiveTamagawa
-- name    : MasulloGRH.tamagawaAdelic_integralOutside_eq_sAdditiveTamagawa
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:50:54.117127+00:00
-- url     : https://prove2.me/theorems/e7af7547-b1ea-468e-b607-2312d79b7769
-- title:
--   Lemma A.3.1.3 — the additive Tamagawa measure is the product of the local ones: $\nu=\nu_S\otimes\bigotimes_{v\notin S}\nu_v$ on $\mathbb A_{F,S}\times\prod_{v\notin S}\mathcal O_{F_v}$
-- statement:
--   **The additive Tamagawa measure is the restricted product of the local additive Tamagawa measures** (Lemma A.3.1.3, first equality of (A.3.1.3) of the source).
--
--   Let $F$ be a number field. For a place $v$ of $F$ let $F_v$ be the completion of $F$ at $v$ and $|\cdot|_v$ the normalized absolute value on $F_v$: the usual absolute value if $F_v\simeq\mathbb R$, its square if $F_v\simeq\mathbb C$, and the absolute value with $|\pi_v|_v=q_v^{-1}$ if $v$ is finite, where $\pi_v$ is a uniformizer of the ring of integers $\mathcal O_{F_v}$ and $q_v=N(\mathfrak p_v)$ is the cardinality of the residue field. The **local additive Tamagawa measure** $\nu_v$ on $F_v$ (Definition A.3.1.2 of the source) is: Lebesgue measure $dx$ if $F_v\simeq\mathbb R$; the measure $|dz\wedge d\bar z|=2\,dx\,dy$ if $F_v\simeq\mathbb C$; and, if $v$ is a finite place above the prime $p$, the Haar measure on $F_v$ with
--   $$\nu_v(\mathcal O_{F_v})=N(\mathfrak d_v)^{-1/2},\qquad N(\mathfrak d_v)=q_v^{d_v},$$
--   where $\mathfrak d_v=\mathfrak d_{F_v/\mathbb Q_p}$ is the local different and $d_v$ is the exponent of the prime $\mathfrak p_v$ in the different $\mathfrak d_{F/\mathbb Q}$ of $F$ (so $d_v=0$ unless $v$ is ramified over $\mathbb Q$, and $\prod_vN(\mathfrak d_v)=|d_F|$ is the absolute value of the discriminant of $F$).
--
--   Let $\mathbb A_F$ be the adele ring of $F$ and $\nu$ the **additive Tamagawa measure** on $\mathbb A_F$ (Definition A.3.1.1; `MasulloGRH.tamagawaAdelic`): the Haar measure for which the compact quotient $\mathbb A_F/F$ has volume $1$, i.e. a measurable fundamental domain for the translation action of $F$ has measure $1$. Let $S$ be a finite set of places of $F$ containing all archimedean places, $S_f$ the set of its finite places, $\mathbb A_{F,S}=\prod_{v\in S}F_v$, and $\nu_S=\bigotimes_{v\in S}\nu_v$ the $S$-local additive Tamagawa measure (`MasulloGRH.sAdditiveTamagawa`).
--
--   Then $\nu=\bigotimes_v\nu_v$ in the sense of restricted products: the restriction of $\nu$ to the open subring $\mathbb A_{F,S}\times\prod_{v\notin S}\mathcal O_{F_v}$ of adeles integral outside $S$ is the product measure $\nu_S\otimes\bigotimes_{v\notin S}\nu_v$. Explicitly, for every Borel set $B\subset\mathbb A_{F,S}$,
--   $$\nu\Big(B\times\prod_{v\notin S}\mathcal O_{F_v}\Big)=\nu_S(B)\cdot\prod_{v\notin S}N(\mathfrak d_v)^{-1/2}=\nu_S(B)\cdot|d_F|^{-1/2}\prod_{v\in S_f}N(\mathfrak d_v)^{1/2},$$
--   where $d_F$ is the discriminant of $F$.
--
--   As every adele is integral outside some finite $S$, these identities for all $S$ determine $\nu$. For $S=S_\infty$ and $B=D_{F,\infty}$ a fundamental parallelepiped of $\mathcal O_F$ in $F\otimes_{\mathbb Q}\mathbb R$ they reduce to $\nu_\infty(D_{F,\infty})=|d_F|^{1/2}$ and $\nu(D_{F,\infty}\times\widehat{\mathcal O}_F)=1$. The lemma identifies the normalization of Haar measure by $\mathrm{vol}(\mathbb A_F/F)=1$, which removes the volume factor from the adelic Poisson summation formula, with the product of the self-dual local measures.
--
--   **Deviation from the source.** Only the first equality of (A.3.1.3) is formalized. The second one, for the measure on $\mathbb A_{F,S}$ normalized by covolume $1$, is false when $S$ omits a ramified place; see `MasulloGRH.sIntegerLattice_covolume_sAdditiveTamagawa` for the covolume of $\mathcal O_{F,S}$.
--
--   **Formalization Note.** $S$ is represented by the finite set `Sf` of its finite places. The set $B\times\prod_{v\notin S}\mathcal O_{F_v}$ is the set of adeles $x$ with $x_v\in\mathcal O_{F_v}$ for all finite $v\notin S$ and whose family of coordinates at the places of $S$ lies in $B$. The infinite product $\prod_{v\notin S}N(\mathfrak d_v)^{-1/2}$ is written in the second form, with $|d_F|$ = `|discr F|` and $N(\mathfrak d_v)$ = `Ideal.absNorm v.asIdeal ^ multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))`. The adele ring carries its Borel $\sigma$-algebra and $\mathbb A_{F,S}$ the product of the Borel $\sigma$-algebras of its factors.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 556, Lemma A.3.1.3, eq. (A.3.1.3) (first equality), with Definition A.3.1.1, p. 555, and Definition A.3.1.2, p. 556; classical reference (cited in the proof, for the archimedean covolume): J.W.S. Cassels, A. Fröhlich, Algebraic Number Theory, London Mathematical Society, 2010, Ch. XV, Lemma 4.1.4

import Mathlib
import Definitions.Def_MasulloGRH_AdelicTheta
import Definitions.Def_MasulloGRH_SLocalTamagawaMeasures

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal

set_option autoImplicit false

namespace MasulloGRH

theorem tamagawaAdelic_integralOutside_eq_sAdditiveTamagawa
    (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (B : Set (SAdeleRing F Sf)) (hB : MeasurableSet B) :
    tamagawaAdelic (F := F)
        {x : AdeleRing (𝓞 F) F |
          (∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf → x.2 v ∈ v.adicCompletionIntegers F) ∧
          ((x.1, fun v : Sf => x.2 (v : HeightOneSpectrum (𝓞 F))) : SAdeleRing F Sf) ∈ B} =
      sAdditiveTamagawa F Sf B *
        ((ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|))⁻¹ *
          ∏ v ∈ Sf, ENNReal.ofReal (Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
            multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))))) := by sorry

end MasulloGRH
