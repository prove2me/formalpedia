-- Prove2me | Theorems.Thm_MasulloGRH_tamagawaAdelic_isAddHaarMeasure_and_fundamentalDomain
-- name    : MasulloGRH.tamagawaAdelic_isAddHaarMeasure_and_fundamentalDomain
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T16:39:24.988023+00:00
-- url     : https://prove2.me/theorems/8dbdd9e6-70eb-49e4-a23b-39aef4d953a4
-- title:
--   Remark 2.2.3.3 / Definition A.3.1.1 — the additive Tamagawa measure $\nu$ on $\mathbb A_F$ is a Haar measure giving every measurable strict fundamental domain of $F$ measure $1$
-- statement:
--   **The additive Tamagawa measure of the adeles** (Remark 2.2.3.3 and Definition A.3.1.1 of the source).
--
--   Let $F$ be a number field and $\mathbb A_F$ its adele ring, a locally compact abelian group in which $F$, embedded diagonally, is a discrete subgroup with compact quotient $\mathbb A_F/F$. The *additive Tamagawa measure* $\nu$ is the Haar measure on $\mathbb A_F$ for which the quotient measure on $\mathbb A_F/F$ (with respect to the counting measure on $F$) has total mass $1$:
--   $$\bar\nu(\mathbb A_F/F)=1.$$
--
--   The statement is that this normalization is meaningful and can be tested on any fundamental domain:
--
--   1. $\nu$ is a Haar measure on $\mathbb A_F$ (positive on non-empty open sets, finite on compact sets, translation invariant);
--   2. for every Borel set $D\subset\mathbb A_F$ that is a strict fundamental domain for $F$, i.e. such that every adele $x$ has exactly one translate $x+\xi$, $\xi\in F$, in $D$, one has
--   $$\nu(D)=1.$$
--
--   By uniqueness of Haar measure these two properties characterize $\nu$. Examples of such $D$ are $[0,1)\times\widehat{\mathbb Z}$ for $F=\mathbb Q$ and, in general, $D_{F,\infty}\times\widehat{\mathcal O}_F$ with $D_{F,\infty}$ a half-open fundamental parallelepiped of the lattice $\mathcal O_F\subset\mathbb A_{F,S_\infty}$.
--
--   This is the normalization of Tate's thesis; the source stresses that it removes all volume factors from the adelic Riemann–Roch theorem (Theorem 2.2.3.2), and it is the measure for which the adelic Fourier transform satisfies inversion without a constant.
--
--   **Formalization Note.** On the platform `MasulloGRH.tamagawaAdelic` is defined by a choice: it is some Haar measure for which some measurable strict fundamental domain has measure $1$ (and the zero measure if there were none). The theorem states that the choice is legitimate and independent of the fundamental domain: `tamagawaAdelic` is an additive Haar measure and *every* measurable strict fundamental domain has measure $1$. The condition "$\bar\nu(\mathbb A_F/F)=1$" of the source is expressed through fundamental domains, which is equivalent by the quotient integral formula.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 82, Remark 2.2.3.3 (On the volume normalization and the global Fourier Transform), and p. 555, Definition A.3.1.1, eq. (A.3.1.1); classical reference cited in Remark 2.2.3.3: J.W.S. Cassels, A. Fröhlich, Algebraic Number Theory, London Mathematical Society, 2010, Ch. XV, §4 (beginning, p. 334)

import Mathlib
import Definitions.Def_MasulloGRH_AdelicTheta

open MeasureTheory NumberField IsDedekindDomain

set_option autoImplicit false

namespace MasulloGRH

theorem tamagawaAdelic_isAddHaarMeasure_and_fundamentalDomain
    (F : Type*) [Field F] [NumberField F] :
    (tamagawaAdelic : Measure (AdeleRing (𝓞 F) F)).IsAddHaarMeasure ∧
    ∀ D : Set (AdeleRing (𝓞 F) F), MeasurableSet D →
      (∀ x : AdeleRing (𝓞 F) F, ∃! ξ : F, x + algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ D) →
      (tamagawaAdelic : Measure (AdeleRing (𝓞 F) F)) D = 1 := by sorry

end MasulloGRH
