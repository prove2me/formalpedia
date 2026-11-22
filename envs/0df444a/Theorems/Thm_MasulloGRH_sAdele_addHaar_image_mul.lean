-- Prove2me | Theorems.Thm_MasulloGRH_sAdele_addHaar_image_mul
-- name    : MasulloGRH.sAdele_addHaar_image_mul
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:49:31.795792+00:00
-- url     : https://prove2.me/theorems/2223d0dc-1e38-4efc-8360-dae03a38a18c
-- title:
--   Lemma A.3.1.4 for $S$-adeles — $\mu(gB)=|g|_{F,S}\,\mu(B)$ for every Haar measure $\mu$ on $\mathbb A_{F,S}$ and every $S$-idele $g$
-- statement:
--   **The modulus of an $S$-idele is its $S$-idelic norm** ($S$-adelic form of Lemma A.3.1.4, eq. (A.3.1.4) of the source).
--
--   Let $F$ be a number field. For a place $v$ of $F$ let $F_v$ be the completion and $|\cdot|_v$ the normalized absolute value on $F_v$: the usual absolute value if $F_v\simeq\mathbb R$, its square if $F_v\simeq\mathbb C$, and the absolute value with $|\pi_v|_v=q_v^{-1}$ if $v$ is finite, with $\pi_v$ a uniformizer and $q_v$ the cardinality of the residue field. Let $S$ be a finite set of places of $F$ containing all archimedean places, and
--   $$\mathbb A_{F,S}=\prod_{v\in S}F_v,\qquad \mathrm{GL}_1(\mathbb A_{F,S})=\prod_{v\in S}F_v^\times,\qquad |g|_{F,S}=\prod_{v\in S}|g_v|_v$$
--   the ring of $S$-adeles (a locally compact ring for the product topology), the group of $S$-ideles and the $S$-idelic norm.
--
--   Let $\mu$ be an arbitrary Haar measure on the additive group of $\mathbb A_{F,S}$. Then for every $S$-idele $g\in\mathrm{GL}_1(\mathbb A_{F,S})$ and every Borel set $B\subset\mathbb A_{F,S}$,
--   $$\mu(gB)=|g|_{F,S}\,\mu(B).$$
--
--   Equivalently $d\mu(gx)=|g|_{F,S}\,d\mu(x)$: the $S$-idelic norm is the modulus of the automorphism $x\mapsto gx$ of $\mathbb A_{F,S}$. The source states this for the full adele ring $\mathbb A_F$ and the idelic norm $|\cdot|_F$ (Lemma A.3.1.4); the $S$-adelic form is the same statement for the finite product $\prod_{v\in S}F_v$ and is what is used for the $S$-local objects: it gives the behaviour of the $S$-local Fourier transform under dilation, $\widehat{f(g\,\cdot)}=|g|_{F,S}^{-1}\hat f(g^{-1}\,\cdot)$, and shows that $|g|_{F,S}^{-1}\,d\nu_S(g)$ is a Haar measure on $\mathrm{GL}_1(\mathbb A_{F,S})$.
--
--   **Formalization Note.** $S$ is represented by the finite set `Sf` of its finite places (`MasulloGRH.SAdeleRing`, `MasulloGRH.SIdeleGroup`, `MasulloGRH.sIdeleNorm`). The measurable structure on $\mathbb A_{F,S}$ is an arbitrary one that is the Borel $\sigma$-algebra (`[BorelSpace]`), so "Borel set" is `MeasurableSet`; $gB$ is the image of $B$ under $x\mapsto gx$, and $|g|_{F,S}>0$ enters through `ENNReal.ofReal`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 556, Lemma A.3.1.4, eq. (A.3.1.4) (stated there for the adele ring; this is the same statement for the S-adeles of §A.1.5 and §A.3.4, p. 561); classical reference (cited in the proof of Lemma A.3.1.4): J.W.S. Cassels, A. Fröhlich, Algebraic Number Theory, London Mathematical Society, 2010, Ch. XV, Lemma 4.1.2

import Mathlib
import Definitions.Def_MasulloGRH_SAdeles

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal

set_option autoImplicit false

namespace MasulloGRH

theorem sAdele_addHaar_image_mul
    (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    [MeasurableSpace (SAdeleRing F Sf)] [BorelSpace (SAdeleRing F Sf)]
    (μ : Measure (SAdeleRing F Sf)) [μ.IsAddHaarMeasure]
    (g : SIdeleGroup F Sf) (B : Set (SAdeleRing F Sf)) (hB : MeasurableSet B) :
    μ ((fun x : SAdeleRing F Sf => (g : SAdeleRing F Sf) * x) '' B) =
      ENNReal.ofReal (sIdeleNorm Sf g) * μ B := by sorry

end MasulloGRH
