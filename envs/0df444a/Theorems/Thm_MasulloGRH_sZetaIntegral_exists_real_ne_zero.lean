-- Prove2me | Theorems.Thm_MasulloGRH_sZetaIntegral_exists_real_ne_zero
-- name    : MasulloGRH.sZetaIntegral_exists_real_ne_zero
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:33:40.693833+00:00
-- url     : https://prove2.me/theorems/dc8153ee-dcb1-499e-b980-bb631e3c6897
-- title:
--   Non-vanishing of $S$-local zeta integrals: every quasi-character $c$ of $\mathrm{GL}_1(\mathbb A_{F,S})$ has a real test function $f\in\mathcal S(\mathbb A_{F,S})$ with $Z_S(f,c)\neq0$
-- statement:
--   **Non-vanishing of the $S$-local zeta integral on real test functions:** for every quasi-character $c$ of the $S$-idele group there is a real-valued $f\in\mathcal S(\mathbb A_{F,S})$ with $Z_S(f,c)\neq0$.
--
--   Let $F$ be a number field and $S$ a finite set of places of $F$ containing all archimedean places. Let $\mathbb A_{F,S}=\prod_{v\in S}F_v$ be the ring of $S$-adeles, $\mathrm{GL}_1(\mathbb A_{F,S})=\prod_{v\in S}F_v^\times$ the group of $S$-ideles, $\mu_S=\bigotimes_{v\in S}\mu_v$ the $S$-local multiplicative Tamagawa measure on $\mathrm{GL}_1(\mathbb A_{F,S})$ and $\mathcal S(\mathbb A_{F,S})$ the Schwartz–Bruhat space of the additive group of $\mathbb A_{F,S}$. For $f\in\mathcal S(\mathbb A_{F,S})$ and a function $c$ on $\mathrm{GL}_1(\mathbb A_{F,S})$ put
--   $$Z_S(f,c)=\int_{\mathrm{GL}_1(\mathbb A_{F,S})}f(g)\,c(g)\,d\mu_S(g).$$
--
--   Let $c\colon\mathrm{GL}_1(\mathbb A_{F,S})\to\mathbb C^\times$ be a quasi-character, i.e. a continuous homomorphism. Then there exists $f\in\mathcal S(\mathbb A_{F,S})$ with
--   $$\overline{f(x)}=f(x)\quad\text{for all }x\in\mathbb A_{F,S}\qquad\text{and}\qquad Z_S(f,c)\neq0 .$$
--
--   The statement shows that the linear functional $f\mapsto Z_S(f,c)$ is not identically zero, even on real test functions; this is what makes the factor $\rho_S(c)$ of the $S$-local functional equation $Z_S(f,c)=\rho_S(c)\,Z_S(\widehat f,\widehat c)$ uniquely determined, and it is the non-vanishing input in the standard derivation (Tate's) of the symmetries $\rho_S(c)\rho_S(\widehat c)=c(-1)$ and $\rho_S(\bar c)=c(-1)\overline{\rho_S(c)}$ of Proposition 3.3.1.5 of the source.
--
--   **Formalization Note.** $S$ is represented by the finite set `Sf` of its finite places. A quasi-character is `MasulloGRH.IsSIdeleQuasiCharacter Sf c` (continuous, multiplicative, nowhere zero); it is not required to be trivial on the $S$-units and no exponent hypothesis is needed. "Real-valued" is `∀ x, conj (f.eval x) = f.eval x`. $Z_S$ is the Bochner integral `MasulloGRH.sZetaIntegral`. It is $0$ when the integrand is not integrable, so the conclusion $Z_S(f,c)\neq0$ also asserts that $f\,c$ is $\mu_S$-integrable.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 132, proof of Proposition 3.3.1.5(1) (auxiliary lemma for the proof of Proposition 3.3.1.5(1)–(2), MasulloGRH.sLocalRho_mul_dual_and_conj)

import Mathlib
import Definitions.Def_MasulloGRH_SLocalZetaIntegrals

open MeasureTheory NumberField IsDedekindDomain

set_option autoImplicit false

namespace MasulloGRH

theorem sZetaIntegral_exists_real_ne_zero
    (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (c : SIdeleGroup F Sf → ℂ) (hc : IsSIdeleQuasiCharacter Sf c) :
    ∃ f : SAdelicSchwartz F Sf,
      (∀ x : SAdeleRing F Sf, (starRingEnd ℂ) (f.eval x) = f.eval x) ∧
        sZetaIntegral f c ≠ 0 := by sorry

end MasulloGRH
