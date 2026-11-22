-- Prove2me | Theorems.Thm_MasulloGRH_sZetaIntegral_continuous
-- name    : MasulloGRH.sZetaIntegral_continuous
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:25:09.34283+00:00
-- url     : https://prove2.me/theorems/3a162b96-b205-4eb6-a77e-10ab1145cee7
-- title:
--   Lemma 3.3.1.3 — for $\sigma(c)>0$ the $S$-local zeta integral $f\mapsto Z_S(f,c)$ is a continuous linear functional on $\mathcal S(\mathbb A_{F,S})$
-- statement:
--   **The $S$-local zeta integrals are tempered distributions** (Lemma 3.3.1.3 of the source).
--
--   Let $F$ be a number field and $S$ a finite set of places of $F$ containing all archimedean places. Let $\mathbb A_{F,S}=\prod_{v\in S}F_v$ be the ring of $S$-adeles, $\mathrm{GL}_1(\mathbb A_{F,S})=\prod_{v\in S}F_v^\times$ the group of $S$-ideles with the $S$-idelic norm $|g|_{F,S}=\prod_{v\in S}|g_v|_v$ (normalized absolute values), $\mu_S=\bigotimes_{v\in S}\mu_v$ the $S$-local multiplicative Tamagawa measure on $\mathrm{GL}_1(\mathbb A_{F,S})$, and $\mathcal S(\mathbb A_{F,S})$ the Schwartz–Bruhat space of $\mathbb A_{F,S}$. A *quasi-character* of $\mathrm{GL}_1(\mathbb A_{F,S})$ is a continuous homomorphism $c:\mathrm{GL}_1(\mathbb A_{F,S})\to\mathbb C^\times$; we assume that it has an *exponent* $\sigma\in\mathbb R$, i.e. $|c(g)|=|g|_{F,S}^{\sigma}$ for all $g$. Every quasi-character of $J_{F,S}=\mathrm{GL}_1(\mathbb A_{F,S})/\mathcal O_{F,S}^\times$ (the case of the source) has one, namely its abscissa $\sigma(c)$. The space $\mathcal S(\mathbb A_{F,S})$ carries its locally convex inductive limit topology.
--
--   Let $c$ be a quasi-character of exponent $\sigma>0$. Then the linear functional
--   $$\mathcal S(\mathbb A_{F,S})\to\mathbb C,\qquad f\mapsto Z_S(f,c)=\int_{\mathrm{GL}_1(\mathbb A_{F,S})}f(g)\,c(g)\,d\mu_S(g)$$
--   is continuous.
--
--   So $Z_S(\cdot,c)$ is a tempered distribution on $\mathbb A_{F,S}$ for every $c$ of positive exponent. This is the starting point of the distributional point of view of the source on zeta integrals (eigendistributions, §3.4.3 and Chapter 5), and it is used to pass from pure tensors to all Schwartz–Bruhat functions.
--
--   **Formalization Note.** A finite set $S\supseteq S_\infty$ of places is represented by the finite set `Sf` of its finite places. Continuity is for the platform topology of `SAdelicSchwartz F Sf` (the finest locally convex topology making the inclusions of the spaces $\mathcal S(k,\Gamma)$ continuous). The quasi-character is not required to be trivial on the $S$-units.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 130, Lemma 3.3.1.3 (proof pp. 130–131)

import Mathlib
import Definitions.Def_MasulloGRH_SLocalZetaIntegrals

open MeasureTheory NumberField IsDedekindDomain

set_option autoImplicit false

namespace MasulloGRH

theorem sZetaIntegral_continuous
    (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (c : SIdeleGroup F Sf → ℂ) (hc : IsSIdeleQuasiCharacter Sf c)
    (σ : ℝ) (hσ : ∀ g : SIdeleGroup F Sf, ‖c g‖ = sIdeleNorm Sf g ^ σ) (h0 : 0 < σ) :
    Continuous (fun f : SAdelicSchwartz F Sf => sZetaIntegral f c) := by sorry

end MasulloGRH
