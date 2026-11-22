-- Prove2me | Theorems.Thm_MasulloGRH_zetaIntegral_eq_sZetaIntegral_mul_partialEulerProduct
-- name    : MasulloGRH.zetaIntegral_eq_sZetaIntegral_mul_partialEulerProduct
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:25:08.209118+00:00
-- url     : https://prove2.me/theorems/df3c83ec-e94e-40d2-a6e6-2b4d99ce69e8
-- title:
--   Theorem 3.4.1.1, eq. (3.4.1.6), corrected — Weil's identity: $Z(f_S\otimes1,\chi|\cdot|_F^s)=Z_S(f_S,\chi_S|\cdot|_{F,S}^s)\prod_{v\notin S}\mu_v(\mathcal O_v^\times)\,L_{\Sigma_F-S}(s,\chi)$
-- statement:
--   **Weil's identity in the unramified case: the global zeta integral is an $S$-local zeta integral times a partial Hecke $L$-function** (Theorem 3.4.1.1, eq. (3.4.1.6), of the source, with the constant that the source omits; the Euler factorization of Tate's zeta integral).
--
--   Let $F$ be a number field and $S$ a finite set of places containing the archimedean places. Let $\chi$ be a Hecke character (a continuous character of $C_F=\mathrm{GL}_1(\mathbb A_F)/F^\times$) unramified at every finite place $v\notin S$, and $\chi(\mathfrak p_v)=\chi_v(\pi_v)$ its value at a uniformizer for such $v$. Let $\chi_S$ be the function on the $S$-ideles $\mathrm{GL}_1(\mathbb A_{F,S})=\prod_{v\in S}F_v^\times$ with $\chi_S((g_v)_{v\in S})=\chi(g)$ for every idele $g$ whose coordinates outside $S$ are units; it is $\chi\circ j_{F,S}$, where $j_{F,S}$ extends an $S$-idele by $1$. Let $f_S\in\mathcal S(\mathbb A_{F,S})$ and let $f=f_S\otimes\bigotimes_{v\notin S}1_{\mathcal O_{F_v}}$ be the function on $\mathbb A_F$
--   $$f(x)=f_S\big((x_v)_{v\in S}\big)\prod_{v\notin S}1_{\mathcal O_{F_v}}(x_v).$$
--   Let $\mu$ be the Tamagawa measure on $\mathrm{GL}_1(\mathbb A_F)$, $\mu_S$ the $S$-local multiplicative Tamagawa measure, and
--   $$Z(f,c)=\int_{\mathrm{GL}_1(\mathbb A_F)}f\,c\,d\mu,\qquad Z_S(f_S,c_S)=\int_{\mathrm{GL}_1(\mathbb A_{F,S})}f_S\,c_S\,d\mu_S.$$
--
--   Then for every $s\in\mathbb C$ with $\operatorname{Re}s>1$ the function $g\mapsto f(g)\chi(g)|g|_F^s$ is $\mu$-integrable and
--   $$Z(f,\chi|\cdot|_F^s)=Z_S(f_S,\chi_S|\cdot|_{F,S}^s)\cdot\Big(\prod_{v\notin S}N(\mathfrak d_v)^{-1/2}\Big)\cdot\prod_{v\notin S}\frac1{1-\chi(\mathfrak p_v)N(\mathfrak p_v)^{-s}},$$
--   where $\mathfrak d_v$ is the local different at $v$, so that $N(\mathfrak d_v)^{-1/2}=\mu_v(\mathcal O_{F_v}^\times)$ and
--   $$\prod_{v\notin S}N(\mathfrak d_v)^{-1/2}=|d_F|^{-1/2}\prod_{v\in S_f}N(\mathfrak d_v)^{1/2},$$
--   and the last product is the partial Hecke $L$-function $L_{\Sigma_F-S}(s,\chi)$.
--
--   The identity reduces the analytic study of the global zeta integrals to the $S$-local ones and to Hecke $L$-functions; the source uses it for the estimates of §3.4.2 and throughout the "global-to-$S$-local" arguments.
--
--   **Deviation from the source.** Equation (3.4.1.6) is printed without the factor $\prod_{v\notin S}\mu_v(\mathcal O_{F_v}^\times)$; it is needed whenever a place outside $S$ is ramified over $\mathbb Q$ (for $F=\mathbb Q(i)$, $S=S_\infty$ it equals $\tfrac12$). The source states the identity for $f_S$ a tensor of an archimedean Schwartz function with indicators of compact open sets and with $S_0=S_\infty\cup S_\chi$; the form here, with an arbitrary $f_S\in\mathcal S(\mathbb A_{F,S})$ and the whole of $S$ on the $S$-local side, contains it. Only the range $\operatorname{Re}s>1$, where everything is given by convergent integrals and products, is stated.
--
--   **Formalization Note.** $S$ is represented by the finite set `Sf` of its finite places. The function $f$ is written as an indicator function times $f_S\circ$`sAdeleRestrict`, and $\chi_S$ is a function `χS` characterized by the hypothesis `hχS` (it is unique, and it exists because $\chi$ is unramified outside $S$). The constant is written as $|d_F|^{-1/2}\prod_{v\in S_f}N(\mathfrak d_v)^{1/2}$ with $N(\mathfrak d_v)=N(\mathfrak p_v)^{m_v}$, $m_v$ the multiplicity of $\mathfrak p_v$ in the different of $F/\mathbb Q$, as in the platform statement of Lemma A.3.2.4. The Euler product is an unconditional infinite product (`tprod`) over the finite places outside $S$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 143, Theorem 3.4.1.1, eq. (3.4.1.6) (proof pp. 143–144); classical reference cited there (p. 142): A. Weil, Fonction zêta et distributions, Séminaire Bourbaki 1965/66, no. 312, §3

import Mathlib
import Definitions.Def_MasulloGRH_ZetaIntegrals
import Definitions.Def_MasulloGRH_SLocalZetaIntegrals

open MeasureTheory NumberField IsDedekindDomain

set_option autoImplicit false

namespace MasulloGRH

theorem zetaIntegral_eq_sZetaIntegral_mul_partialEulerProduct
    (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (fS : SAdelicSchwartz F Sf) (χ : HeckeCharacter F)
    (hχ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf → χ.IsUnramifiedAt v)
    (χS : SIdeleGroup F Sf → ℂ)
    (hχS : ∀ g : IdeleGroup F, g ∈ sIntegralIdeles Sf →
      χS (sIdeleRestrict Sf g) = ((χ (QuotientGroup.mk g) : Circle) : ℂ))
    (s : ℂ) (hs : 1 < s.re) :
    Integrable
      (fun g : IdeleGroup F =>
        Set.indicator
          {x : AdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf →
            x.2 v ∈ v.adicCompletionIntegers F}
          (fun x : AdeleRing (𝓞 F) F => fS.eval (sAdeleRestrict Sf x)) (g : AdeleRing (𝓞 F) F) *
          quasiTwist (fun g : IdeleGroup F => ((χ (QuotientGroup.mk g) : Circle) : ℂ)) s g)
      (tamagawaIdele F) ∧
    zetaIntegralFun
        (Set.indicator
          {x : AdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf →
            x.2 v ∈ v.adicCompletionIntegers F}
          (fun x : AdeleRing (𝓞 F) F => fS.eval (sAdeleRestrict Sf x)))
        (quasiTwist (fun g : IdeleGroup F => ((χ (QuotientGroup.mk g) : Circle) : ℂ)) s) =
      sZetaIntegral fS (sQuasiTwist Sf χS s) *
        (((Real.sqrt |(discr F : ℝ)|)⁻¹ *
          ∏ v ∈ Sf, Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
            multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))) : ℝ) : ℂ) *
        ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ Sf},
          (1 - χ.primeValue (v : HeightOneSpectrum (𝓞 F)) *
            ((Ideal.absNorm (v : HeightOneSpectrum (𝓞 F)).asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ := by sorry

end MasulloGRH
