-- Prove2me | Theorems.Thm_MasulloGRH_stdAdelicCharacter_pontryaginDual_equiv
-- name    : MasulloGRH.stdAdelicCharacter_pontryaginDual_equiv
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:28:18.64222+00:00
-- url     : https://prove2.me/theorems/a721e112-0227-4604-94aa-3bd7a63e9148
-- title:
--   Examples A.3.1.8–A.3.1.9 — self-duality of the adeles: $y\mapsto\psi_{F,\mathrm{std}}(\cdot\,y)$ is an isomorphism of topological groups $\mathbb A_F\cong\widehat{\mathbb A_F}$
-- statement:
--   **Self-duality of the adeles: $y\mapsto\psi_{F,\mathrm{std}}(\,\cdot\,y)$ identifies $\mathbb A_F$ with its Pontryagin dual** (Examples A.3.1.8–A.3.1.9 of the source).
--
--   Let $F$ be a number field and $\mathbb A_F$ its adele ring, the restricted product of the completions $F_v$ over all places $v$ of $F$ with respect to the rings of integers $\mathcal O_{F_v}$ at the finite places, with its restricted product topology; it is a Hausdorff locally compact abelian group under addition. Let $\psi=\psi_{F,\mathrm{std}}=\psi_{\mathbb Q,\mathrm{std}}\circ\mathrm{Tr}_{F/\mathbb Q}\colon\mathbb A_F\to\mathrm U(1)$ be the standard additive character (eq. (A.3.1.7), in the sign convention of Tate's thesis; `MasulloGRH.stdAdelicCharacter`): it is the product of the local characters $\psi_w(x)=e^{-2\pi i\,\mathrm{Tr}_{F_w/\mathbb R}(x)}$ at the archimedean places $w$ and $\psi_v(x)=e^{2\pi i\{\mathrm{Tr}_{F_v/\mathbb Q_p}(x)\}_p}$ at the finite places $v\mid p$, and it is trivial on $F$. Let $\widehat{\mathbb A_F}$ be the Pontryagin dual of $\mathbb A_F$: the group of continuous homomorphisms $\mathbb A_F\to\mathrm U(1)$ with the compact-open topology.
--
--   Then for every $y\in\mathbb A_F$ the function
--   $$\chi_y(x)=\psi(xy)\qquad(x\in\mathbb A_F)$$
--   is a continuous character of $\mathbb A_F$, and
--   $$\mathbb A_F\longrightarrow\widehat{\mathbb A_F},\qquad y\longmapsto\chi_y,$$
--   is an isomorphism of topological groups.
--
--   This is the theorem of Tate's thesis that the adele ring is naturally its own character group. It is the identification under which the Fourier transform $\widehat f(y)=\int_{\mathbb A_F}f(x)\psi(xy)\,d\nu(x)$ of a function on $\mathbb A_F$ is again a function on $\mathbb A_F$, so that the general Fourier isomorphism $\mathcal S(G)\cong\mathcal S(\widehat G)$ of Schwartz–Bruhat spaces becomes an automorphism of $\mathcal S(\mathbb A_F)$ (Theorem 2.2.3.2 and Remark 2.2.3.3 of the source), and under which the self-duality of the Tamagawa measure (Example A.3.1.9) is formulated.
--
--   **Deviation from the source.** At the archimedean places the standard character is taken with the sign of Tate's thesis, $\psi_w(x)=e^{-2\pi i\,\mathrm{Tr}_{F_w/\mathbb R}(x)}$, whereas Example A.3.1.5 of the source prints $e^{+2\pi i\,\mathrm{Tr}_{F_w/\mathbb R}(x)}$, from which (A.3.1.7) is built; with the printed signs the product of the local characters is not trivial on $F$ (for $F=\mathbb Q$ its value at $1/3$ is $e^{4\pi i/3}$). This is the convention of the platform definition `MasulloGRH.stdAdelicCharacter` and of `MasulloGRH.tamagawaAdelic_selfDual_stdAdelicCharacter`. The self-duality asserted here holds for either sign.
--
--   **Formalization Note.** $\mathbb A_F$ is Mathlib's `NumberField.AdeleRing (𝓞 F) F` (infinite adeles times finite adeles), and its additive group is written multiplicatively (`Multiplicative`) as Mathlib's `PontryaginDual` requires; `PontryaginDual` carries the compact-open topology and `≃ₜ*` is an isomorphism of topological groups. The statement asserts the existence of such an isomorphism $e$ with $e(y)(x)=\psi_{F,\mathrm{std}}(xy)$, which determines $e$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 558, Examples A.3.1.8–A.3.1.9 (the self-duality of $\mathbb A_F$ defined by the standard character $\psi_{F,\mathrm{std}}$, eq. (A.3.1.7)); auxiliary lemma for the proof of Theorem 2.2.3.2 and Remark 2.2.3.3, p. 82 (MasulloGRH.adelicFourier_schwartzBruhat_equiv); classical reference (cited in Example A.3.1.9): J. Tate, Fourier analysis in number fields and Hecke's zeta-functions, in J. W. S. Cassels, A. Fröhlich (eds.), Algebraic Number Theory, Ch. XV, §4.1 (global additive characters: the adele ring is naturally its own character group)

import Mathlib
import Definitions.Def_MasulloGRH_AdelicTheta

open NumberField IsDedekindDomain

set_option autoImplicit false

namespace MasulloGRH

theorem stdAdelicCharacter_pontryaginDual_equiv
    (F : Type*) [Field F] [NumberField F] :
    ∃ e : Multiplicative (AdeleRing (𝓞 F) F) ≃ₜ*
        PontryaginDual (Multiplicative (AdeleRing (𝓞 F) F)),
      ∀ x y : AdeleRing (𝓞 F) F,
        ((e (Multiplicative.ofAdd y) (Multiplicative.ofAdd x) : Circle) : ℂ) =
          stdAdelicCharacter (x * y) := by sorry

end MasulloGRH
