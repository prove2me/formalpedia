-- Prove2me | Theorems.Thm_MasulloGRH_sLocalFourier_schwartzBruhat_equiv
-- name    : MasulloGRH.sLocalFourier_schwartzBruhat_equiv
-- status  : Open
-- author  : @emmgaml
-- created : 2026-11-22T15:24:58.002385+00:00
-- url     : https://prove2.me/theorems/c0b1677b-b851-4e60-adb5-87a64e136508
-- title:
--   §3.3.1 — the $S$-adelic Fourier transform is a linear topological automorphism of $\mathcal S(\mathbb A_{F,S})$, with $\widehat{\widehat f}(x)=f(-x)$
-- statement:
--   **The $S$-adelic Fourier transform on the Schwartz–Bruhat space** (§3.3.1 of the source, first paragraphs).
--
--   Let $F$ be a number field and $S$ a finite set of places of $F$ containing all archimedean places. Let $\mathbb A_{F,S}=\prod_{v\in S}F_v$ be the ring of $S$-adeles, $\mathrm{GL}_1(\mathbb A_{F,S})=\prod_{v\in S}F_v^\times$ the group of $S$-ideles with the $S$-idelic norm $|g|_{F,S}=\prod_{v\in S}|g_v|_v$ (normalized absolute values), $\mu_S=\bigotimes_{v\in S}\mu_v$ the $S$-local multiplicative Tamagawa measure on $\mathrm{GL}_1(\mathbb A_{F,S})$, and $\mathcal S(\mathbb A_{F,S})$ the Schwartz–Bruhat space of $\mathbb A_{F,S}$. Let $\nu_S=\bigotimes_{v\in S}\nu_v$ be the $S$-local additive Tamagawa measure on $\mathbb A_{F,S}$ and $\psi_{S,\mathrm{std}}$ the standard additive character of $\mathbb A_{F,S}$. For $f\in\mathcal S(\mathbb A_{F,S})$ the Fourier transform is
--   $$\widehat f(y)=\int_{\mathbb A_{F,S}}f(x)\,\psi_{S,\mathrm{std}}(xy)\,d\nu_S(x).$$
--
--   Then:
--
--   1. every $f\in\mathcal S(\mathbb A_{F,S})$ is $\nu_S$-integrable;
--   2. $f\mapsto\widehat f$ maps $\mathcal S(\mathbb A_{F,S})$ into itself and is a $\mathbb C$-linear homeomorphism of $\mathcal S(\mathbb A_{F,S})$ onto itself, for its locally convex (inductive limit) topology;
--   3. Fourier inversion holds without a normalizing constant: $\widehat{\widehat f}(x)=f(-x)$ for all $x\in\mathbb A_{F,S}$.
--
--   Item 3 expresses that $\nu_S$ is self-dual for $\psi_{S,\mathrm{std}}$. The statement is the $S$-adelic case of the theorem that the Fourier transform is a topological isomorphism $\mathcal S(G)\to\mathcal S(\widehat G)$ for a locally compact abelian group $G$, combined with the self-duality $\mathbb A_{F,S}\cong\widehat{\mathbb A_{F,S}}$, $y\mapsto\psi_{S,\mathrm{std}}(\,\cdot\,y)$. It is what makes the dual side $Z_S(\widehat f,\widehat c)$ of the $S$-local functional equation meaningful.
--
--   **Formalization Note.** A finite set $S\supseteq S_\infty$ of places is represented by the finite set `Sf` of its finite places. The automorphism is a continuous linear equivalence `T` of the platform space `SAdelicSchwartz F Sf` whose underlying function is the integral above, `(T f).eval = sLocalFourier Sf f.eval`; inversion is stated as `(T (T f)).eval x = f.eval (-x)`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 128, §3.3.1 (first three paragraphs); classical reference cited there for Fourier inversion: D. Ramakrishnan, R. J. Valenza, Fourier Analysis on Number Fields, Springer, Prop. 5.6(iii), p. 186

import Mathlib
import Definitions.Def_MasulloGRH_SLocalZetaIntegrals

open MeasureTheory NumberField IsDedekindDomain

set_option autoImplicit false

namespace MasulloGRH

theorem sLocalFourier_schwartzBruhat_equiv
    (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    (∀ f : SAdelicSchwartz F Sf, Integrable f.eval (sAdditiveTamagawa F Sf)) ∧
    ∃ T : SAdelicSchwartz F Sf ≃L[ℂ] SAdelicSchwartz F Sf,
      (∀ f : SAdelicSchwartz F Sf, (T f).eval = sLocalFourier Sf f.eval) ∧
      ∀ (f : SAdelicSchwartz F Sf) (x : SAdeleRing F Sf), (T (T f)).eval x = f.eval (-x) := by sorry

end MasulloGRH
