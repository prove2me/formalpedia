-- Prove2me | Theorems.Thm_MasulloGRH_tamagawaAdelic_selfDual_stdAdelicCharacter
-- name    : MasulloGRH.tamagawaAdelic_selfDual_stdAdelicCharacter
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T16:39:53.669802+00:00
-- url     : https://prove2.me/theorems/025e8761-e426-48d0-9994-9a9d4dee25ea
-- title:
--   Examples A.3.1.8–A.3.1.9 — $\psi_{F,\mathrm{std}}$ is a non-trivial continuous unitary character of $\mathbb A_F$, trivial on $F$, and the Tamagawa measure $\nu$ is self-dual for it
-- statement:
--   **The standard additive character of the adeles and the self-duality of the Tamagawa measure** (Examples A.3.1.8–A.3.1.9 of the source, used in Theorem 2.2.3.2 and Remark 2.2.3.3).
--
--   Let $F$ be a number field, $\mathbb A_F$ its adele ring and $\nu$ the additive Tamagawa measure on $\mathbb A_F$, the Haar measure with $\bar\nu(\mathbb A_F/F)=1$. The *standard additive character* is
--   $$\psi=\psi_{F,\mathrm{std}}=\psi_{\mathbb Q,\mathrm{std}}\circ\mathrm{Tr}_{F/\mathbb Q},\qquad \psi_{\mathbb Q,\mathrm{std}}(x)=e^{-2\pi i\,x_\infty}\prod_pe^{2\pi i\{x_p\}_p},$$
--   where $\{\cdot\}_p$ is the $p$-adic fractional part. For a function $f$ on $\mathbb A_F$ put
--   $$\widehat f(y)=\int_{\mathbb A_F}f(x)\,\psi(xy)\,d\nu(x).$$
--
--   Then:
--
--   1. $\psi$ is a continuous unitary character of the additive group $\mathbb A_F$: $\psi(x+y)=\psi(x)\psi(y)$, $|\psi(x)|=1$, and $\psi$ is continuous;
--   2. $\psi$ is trivial on the diagonally embedded field: $\psi(\xi)=1$ for all $\xi\in F$; and $\psi$ is not the trivial character;
--   3. (self-duality) $\nu$ is the Plancherel measure of $\mathbb A_F$ for the identification of $\mathbb A_F$ with its Pontryagin dual given by $y\mapsto\psi(\,\cdot\,y)$: if $f\colon\mathbb A_F\to\mathbb C$ is continuous and $\nu$-integrable and $\widehat f$ is $\nu$-integrable, then for every $z\in\mathbb A_F$
--   $$\widehat{\widehat f}(z)=f(-z),$$
--   with no normalizing constant.
--
--   Properties 1–2 say that $\psi$ is a non-trivial character of the compact group $\mathbb A_F/F$; property 3 is the theorem of Tate's thesis that the measure with $\bar\nu(\mathbb A_F/F)=1$ is self-dual. Together they are the input of the adelic Poisson summation formula and of the Riemann–Roch theorem (Theorem 2.2.3.2 of the source).
--
--   **Deviation from the source.** With the local characters as printed in Examples A.3.1.5–A.3.1.6 (the same sign at the real and at the $p$-adic places) the product is not trivial on $\mathbb Q$ (its value at $1/3$ is $e^{4\pi i/3}$). The character used here has opposite signs at the archimedean and the finite places, as in Tate's thesis; this is the convention of the platform definition.
--
--   **Formalization Note.** `MasulloGRH.stdAdelicCharacter` is a complex-valued function defined through a decomposition of an adele as an integral adele plus an element of $F$, and `MasulloGRH.tamagawaAdelic` is defined by a choice; items 1–2 record that the function is the character described above. $\widehat f$ is `MasulloGRH.adelicFourierFun f`. Self-duality is stated in the source's sense (Fourier inversion without constant), for continuous integrable functions with integrable transform.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 558, Examples A.3.1.8–A.3.1.9, eq. (A.3.1.7) (with the sign convention of Tate's thesis), as used on p. 82, Theorem 2.2.3.2 and Remark 2.2.3.3; classical reference cited in Example A.3.1.9: J.W.S. Cassels, A. Fröhlich, Algebraic Number Theory, London Mathematical Society, 2010, Ch. XV, §4.1, Thm. 4.1.2

import Mathlib
import Definitions.Def_MasulloGRH_AdelicTheta

open MeasureTheory NumberField IsDedekindDomain

set_option autoImplicit false

namespace MasulloGRH

theorem tamagawaAdelic_selfDual_stdAdelicCharacter
    (F : Type*) [Field F] [NumberField F] :
    (∀ x y : AdeleRing (𝓞 F) F,
      stdAdelicCharacter (x + y) = stdAdelicCharacter x * stdAdelicCharacter y) ∧
    (∀ x : AdeleRing (𝓞 F) F, ‖stdAdelicCharacter x‖ = 1) ∧
    Continuous (stdAdelicCharacter : AdeleRing (𝓞 F) F → ℂ) ∧
    (∀ ξ : F, stdAdelicCharacter (algebraMap F (AdeleRing (𝓞 F) F) ξ) = 1) ∧
    (∃ x : AdeleRing (𝓞 F) F, stdAdelicCharacter x ≠ 1) ∧
    ∀ f : AdeleRing (𝓞 F) F → ℂ, Continuous f → Integrable f tamagawaAdelic →
      Integrable (adelicFourierFun f) tamagawaAdelic →
      ∀ z : AdeleRing (𝓞 F) F, adelicFourierFun (adelicFourierFun f) z = f (-z) := by sorry

end MasulloGRH
