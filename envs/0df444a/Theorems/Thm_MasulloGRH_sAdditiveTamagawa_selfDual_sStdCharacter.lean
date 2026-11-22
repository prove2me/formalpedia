-- Prove2me | Theorems.Thm_MasulloGRH_sAdditiveTamagawa_selfDual_sStdCharacter
-- name    : MasulloGRH.sAdditiveTamagawa_selfDual_sStdCharacter
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:51:10.022812+00:00
-- url     : https://prove2.me/theorems/3645b047-b22b-4bee-a24e-b8ddc1a27188
-- title:
--   Example A.3.1.11 and Remark A.3.4.2 — $\psi_{S,\mathrm{std}}$ is a unitary character of $\mathbb A_{F,S}$ and $\nu_S$ is self-dual for it: Fourier inversion $\hat{\hat f}(x)=f(-x)$
-- statement:
--   **Self-duality of the $S$-local additive Tamagawa measure** (Example A.3.1.11 and Remark A.3.4.2 of the source).
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
--   Let $\nu_S=\bigotimes_{v\in S}\nu_v$ be the $S$-local additive Tamagawa measure on $\mathbb A_{F,S}$ (Definition A.3.4.1(1); `MasulloGRH.sAdditiveTamagawa`) and $\psi_{S,\mathrm{std}}=\bigotimes_{v\in S}\psi_v$ the standard additive character (eq. (A.3.1.9); `MasulloGRH.sStdCharacter`), the product of $\psi_w(x)=e^{-2\pi i\,\mathrm{Tr}_{F_w/\mathbb R}(x)}$ ($w\mid\infty$) and $\psi_v(x)=e^{2\pi i\{\mathrm{Tr}_{F_v/\mathbb Q_p}(x)\}_p}$ ($v\mid p$ finite). For an integrable function $f$ on $\mathbb A_{F,S}$ let
--   $$\hat f(y)=\int_{\mathbb A_{F,S}}f(x)\,\psi_{S,\mathrm{std}}(xy)\,d\nu_S(x)\qquad(y\in\mathbb A_{F,S})$$
--   be its Fourier transform. Then:
--
--   1. $\psi_{S,\mathrm{std}}$ is a continuous unitary character of the additive group of $\mathbb A_{F,S}$: $\psi_{S,\mathrm{std}}(x+y)=\psi_{S,\mathrm{std}}(x)\,\psi_{S,\mathrm{std}}(y)$, $|\psi_{S,\mathrm{std}}(x)|=1$, and $\psi_{S,\mathrm{std}}$ is continuous;
--   2. $\nu_S$ is **self-dual** with respect to the pairing $\langle x,y\rangle_S=\psi_{S,\mathrm{std}}(xy)$, i.e. Fourier inversion holds with no correcting constant: for every continuous integrable function $f\colon\mathbb A_{F,S}\to\mathbb C$ whose Fourier transform $\hat f$ is integrable,
--   $$\hat{\hat f}(z)=\int_{\mathbb A_{F,S}}\hat f(y)\,\psi_{S,\mathrm{std}}(yz)\,d\nu_S(y)=f(-z)\qquad\text{for all }z\in\mathbb A_{F,S}.$$
--
--   In the words of the source, $x\mapsto\psi_{S,\mathrm{std}}(x\,\cdot)$ identifies $\mathbb A_{F,S}$ with its Pontryagin dual and "this makes $\nu_S$ self-dual (i.e., its own Plancherel measure) due to the same for each $(\psi_v,\nu_v)$": Lebesgue measure on $\mathbb R$, the measure $2\,dx\,dy$ on $\mathbb C$, and the Haar measure with $\nu_v(\mathcal O_{F_v})=N(\mathfrak d_v)^{-1/2}$ on $F_v$ are the self-dual measures for the standard characters. Consequently the $S$-local Fourier transform extends to a unitary operator of $L^2(\mathbb A_{F,S},\nu_S)$.
--
--   **Deviation from the source.** The standard character is taken with the sign convention of Tate's thesis (see `MasulloGRH.sStdCharacter`); the self-duality of $\nu_S$ does not depend on this choice of sign. The Fourier transform is written with $\psi_{S,\mathrm{std}}(xy)$, as in the platform definition `MasulloGRH.adelicFourierFun`, whereas the source writes Fourier transforms with the complex conjugate $\overline{\psi(xy)}$ (e.g. in Example A.3.1.7, p. 558); the inversion formula $\hat{\hat f}(z)=f(-z)$ is the same for both.
--
--   **Formalization Note.** $S$ is represented by the finite set `Sf` of its finite places. Integrals are Bochner integrals with respect to `MasulloGRH.sAdditiveTamagawa F Sf`, and `sStdCharacter` is complex-valued. The hypotheses of part 2 are those of the Fourier inversion theorem for locally compact abelian groups: $f$ continuous, $f\in L^1$, $\hat f\in L^1$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 558–559, Example A.3.1.11, eqs. (A.3.1.9)–(A.3.1.10); p. 562, Remark A.3.4.2 (first paragraph); classical reference (cited in Example A.3.1.5, p. 557, for the self-duality of the local measures): J.W.S. Cassels, A. Fröhlich, Algebraic Number Theory, London Mathematical Society, 2010, Ch. XV, §2.2, Thm. 2.2.2

import Mathlib
import Definitions.Def_MasulloGRH_SLocalTamagawaMeasures
import Definitions.Def_MasulloGRH_SLocalStandardCharacter

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal

set_option autoImplicit false

namespace MasulloGRH

theorem sAdditiveTamagawa_selfDual_sStdCharacter
    (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    (∀ x y : SAdeleRing F Sf,
      sStdCharacter Sf (x + y) = sStdCharacter Sf x * sStdCharacter Sf y) ∧
    (∀ x : SAdeleRing F Sf, ‖sStdCharacter Sf x‖ = 1) ∧
    Continuous (sStdCharacter Sf : SAdeleRing F Sf → ℂ) ∧
    ∀ f : SAdeleRing F Sf → ℂ, Continuous f → Integrable f (sAdditiveTamagawa F Sf) →
      Integrable (fun y : SAdeleRing F Sf =>
        ∫ x, f x * sStdCharacter Sf (x * y) ∂(sAdditiveTamagawa F Sf)) (sAdditiveTamagawa F Sf) →
      ∀ z : SAdeleRing F Sf,
        ∫ y, (∫ x, f x * sStdCharacter Sf (x * y) ∂(sAdditiveTamagawa F Sf)) *
            sStdCharacter Sf (y * z) ∂(sAdditiveTamagawa F Sf) = f (-z) := by sorry

end MasulloGRH
