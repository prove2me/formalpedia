-- Prove2me | Theorems.Thm_MasulloGRH_tendsto_sum_heckeCharacter_ideals_div_atTop
-- name    : MasulloGRH.tendsto_sum_heckeCharacter_ideals_div_atTop
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:31:43.16209+00:00
-- url     : https://prove2.me/theorems/4477b03f-d0a4-4b33-90b0-85a39d4dafed
-- title:
--   Lemma B.6.1.2(2) — $\sum_{N(I)\le x}\chi(I)=o(x)$ for a Hecke character $\chi$ that is non-trivial on $C_F^1$
-- statement:
--   **Lemma B.6.1.2(2) (partial sums of a non-trivial Hecke character over integral ideals).** Let $F$ be a number field and $\chi\colon C_F\to U(1)$ a Hecke character, i.e. a continuous character of the idele class group $C_F=\mathrm{GL}_1(\mathbb A_F)/F^\times$. For a finite place $v$ with prime ideal $\mathfrak p_v$ let $\chi(\mathfrak p_v)$ be the value of $\chi$ at a uniformizer of $F_v$ if $\chi$ is unramified at $v$, and $0$ if $\chi$ is ramified at $v$; extend $\chi$ multiplicatively to the nonzero ideals of $\mathcal O_F$,
--   $$\chi(I)=\prod_v\chi(\mathfrak p_v)^{\operatorname{ord}_v(I)},$$
--   so that $\chi(I)=0$ when $I$ is not coprime to the conductor of $\chi$. These are the coefficients of the finite Hecke $L$-function, $L_f(s,\chi)=\sum_{0\ne I\subset\mathcal O_F}\chi(I)N(I)^{-s}$ for $\operatorname{Re}(s)>1$ (eq. (B.6.1.2)). Let
--   $$S_{F,\chi}(x)=\sum_{0\ne I\subset\mathcal O_F,\ N(I)\le x}\chi(I)$$
--   be the summatory function (eq. (B.6.1.3)). If the restriction of $\chi$ to the subgroup $C_F^1$ of idele classes of norm $1$ is non-trivial, then
--   $$\frac{S_{F,\chi}(x)}{x}\longrightarrow0\qquad(x\to+\infty).$$
--
--   This is equation (B.6.1.8) of the source. It is the counterpart for non-trivial characters of the ideal counting theorem $\#\{I:N(I)\le x\}\sim\kappa_Fx$ (part (1) of the lemma, which is in Mathlib as `NumberField.Ideal.tendsto_norm_le_div_atTop`); the source derives it from the holomorphy of $L_f(s,\chi)$ on a neighbourhood of $\operatorname{Re}(s)\ge1$ by the Tauberian theorem [MVa, Cor. 8.8], the coefficients being dominated by those of $\zeta_F$.
--
--   **Formalization Note.** Built on the platform definitions `MasulloGRH.HeckeCharacter` (Pontryagin dual of the idele class group), `HeckeCharacter.primeValue` (the number $\chi(\mathfrak p_v)$ above) and `HeckeCharacter.IsTrivialOnNormOne` ($\chi|_{C_F^1}=1$) from `Def_MasulloGRH_HeckeLFunction` and `Def_MasulloGRH_IdeleNorm`. The value $\chi(I)$ is written inline as the `finprod` over the finite places $v$ of `χ.primeValue v` raised to the multiplicity of $\mathfrak p_v$ in the prime factorization `UniqueFactorizationMonoid.normalizedFactors I` of the ideal $I$ (all but finitely many factors are $1$); the sum is a `finsum` over the ideals `I ≠ ⊥` with `(Ideal.absNorm I : ℝ) ≤ x`, a finite set. The limit is taken in $\mathbb C$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 637, Lemma B.6.1.2(2), eq. (B.6.1.8); classical reference: H. Montgomery and R. C. Vaughan, Multiplicative Number Theory I, Cambridge Studies in Advanced Mathematics, 2006, Corollary 8.8 (the Tauberian theorem from which the source deduces it)

import Mathlib
import Definitions.Def_MasulloGRH_IdeleNorm

open Filter Topology NumberField IsDedekindDomain

set_option autoImplicit false

namespace MasulloGRH

theorem tendsto_sum_heckeCharacter_ideals_div_atTop
    (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F)
    (hχ : ¬ χ.IsTrivialOnNormOne) :
    Tendsto
      (fun x : ℝ =>
        (∑ᶠ (I : Ideal (𝓞 F)) (_ : I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ x),
          ∏ᶠ v : HeightOneSpectrum (𝓞 F),
            χ.primeValue v ^
              Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors I)) / (x : ℂ))
      atTop (𝓝 0) := by sorry

end MasulloGRH
