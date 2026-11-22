-- Prove2me | Theorems.Thm_MasulloGRH_sStdCharacter_pontryaginDual_equiv
-- name    : MasulloGRH.sStdCharacter_pontryaginDual_equiv
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:34:18.535314+00:00
-- url     : https://prove2.me/theorems/e151ee95-3542-49d3-9cc8-6f02c326453f
-- title:
--   Example A.3.1.11 — self-duality of the $S$-adeles: $y\mapsto\psi_{S,\mathrm{std}}(\cdot\,y)$ is an isomorphism of topological groups $\mathbb A_{F,S}\cong\widehat{\mathbb A_{F,S}}$
-- statement:
--   **Self-duality of the $S$-adeles: $y\mapsto\psi_{S,\mathrm{std}}(\,\cdot\,y)$ identifies $\mathbb A_{F,S}$ with its Pontryagin dual** (Example A.3.1.11 of the source).
--
--   Let $F$ be a number field and $S$ a finite set of places of $F$ containing all archimedean places. Let
--   $$\mathbb A_{F,S}=\prod_{v\in S}F_v$$
--   be the ring of $S$-adeles, with the product topology of the completions $F_v$; it is a Hausdorff locally compact abelian group under addition. Let $\psi_{S,\mathrm{std}}=\bigotimes_{v\in S}\psi_v\colon\mathbb A_{F,S}\to\mathrm U(1)$ be the standard additive character (eq. (A.3.1.9), in the sign convention of Tate's thesis; `MasulloGRH.sStdCharacter`), the product of the local standard characters $\psi_w(x)=e^{-2\pi i\,\mathrm{Tr}_{F_w/\mathbb R}(x)}$ at the archimedean places $w$ and $\psi_v(x)=e^{2\pi i\{\mathrm{Tr}_{F_v/\mathbb Q_p}(x)\}_p}$ at the finite places $v\mid p$ of $S$. Let $\widehat{\mathbb A_{F,S}}$ be the Pontryagin dual of $\mathbb A_{F,S}$: the group of continuous homomorphisms $\mathbb A_{F,S}\to\mathrm U(1)$ with the compact-open topology.
--
--   Then for every $y\in\mathbb A_{F,S}$ the function
--   $$\chi_y(x)=\psi_{S,\mathrm{std}}(xy)\qquad(x\in\mathbb A_{F,S})$$
--   is a continuous character of $\mathbb A_{F,S}$, and
--   $$\mathbb A_{F,S}\longrightarrow\widehat{\mathbb A_{F,S}},\qquad y\longmapsto\chi_y,$$
--   is an isomorphism of topological groups.
--
--   This is the $S$-adelic form of the self-duality $F_v\cong\widehat{F_v}$, $a\mapsto\psi_v(a\,\cdot)$, of the local fields, combined with $\widehat{G_1\times G_2}=\widehat{G_1}\times\widehat{G_2}$ for finitely many factors. It is the identification under which the Fourier transform $\widehat f(y)=\int f(x)\psi_{S,\mathrm{std}}(xy)\,d\nu_S(x)$ of a function on $\mathbb A_{F,S}$ is again a function on $\mathbb A_{F,S}$, so that the general Fourier isomorphism $\mathcal S(G)\cong\mathcal S(\widehat G)$ of Schwartz–Bruhat spaces becomes an automorphism of $\mathcal S(\mathbb A_{F,S})$ (§3.3.1 of the source).
--
--   **Deviation from the source.** At the archimedean places the standard character is taken with the sign of Tate's thesis, $\psi_w(x)=e^{-2\pi i\,\mathrm{Tr}_{F_w/\mathbb R}(x)}$, whereas Example A.3.1.5 of the source prints $e^{+2\pi i\,\mathrm{Tr}_{F_w/\mathbb R}(x)}$; with this choice the global standard character is trivial on $F$ (see `MasulloGRH.sStdCharacter`). The self-duality asserted here holds for either sign. Example A.3.1.11 also assumes that $S$ contains every place of $F$ ramified over $\mathbb Q$; that assumption is not needed for the self-duality and is not made here.
--
--   **Formalization Note.** $S$ is represented by the finite set `Sf` of its finite places, $\mathbb A_{F,S}$ is `MasulloGRH.SAdeleRing F Sf`, and the additive group is written multiplicatively (`Multiplicative`) as Mathlib's `PontryaginDual` requires; `PontryaginDual` carries the compact-open topology and `≃ₜ*` is an isomorphism of topological groups. The statement asserts the existence of such an isomorphism $e$ with $e(y)(x)=\psi_{S,\mathrm{std}}(xy)$, which determines $e$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 559, Example A.3.1.11 (the sentence after eq. (A.3.1.9): the assignment $x\mapsto\chi_x$ is an isomorphism $\mathbb A_{F,S}\to\widehat{\mathbb A_{F,S}}$ of Hausdorff locally compact abelian groups); auxiliary lemma for the proof of the statement of §3.3.1, p. 128 (MasulloGRH.sLocalFourier_schwartzBruhat_equiv); classical reference for the local case: J. Tate, Fourier analysis in number fields and Hecke's zeta-functions, in J. W. S. Cassels, A. Fröhlich (eds.), Algebraic Number Theory, Ch. XV, §2.2

import Mathlib
import Definitions.Def_MasulloGRH_SLocalStandardCharacter

open NumberField IsDedekindDomain

set_option autoImplicit false

namespace MasulloGRH

theorem sStdCharacter_pontryaginDual_equiv
    (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ e : Multiplicative (SAdeleRing F Sf) ≃ₜ* PontryaginDual (Multiplicative (SAdeleRing F Sf)),
      ∀ x y : SAdeleRing F Sf,
        ((e (Multiplicative.ofAdd y) (Multiplicative.ofAdd x) : Circle) : ℂ) =
          sStdCharacter Sf (x * y) := by sorry

end MasulloGRH
