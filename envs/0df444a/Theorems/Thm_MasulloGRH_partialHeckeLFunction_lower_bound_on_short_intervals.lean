-- Prove2me | Theorems.Thm_MasulloGRH_partialHeckeLFunction_lower_bound_on_short_intervals
-- name    : MasulloGRH.partialHeckeLFunction_lower_bound_on_short_intervals
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-21T03:45:05.097729+00:00
-- url     : https://prove2.me/theorems/6ef66fe4-1e61-4802-9361-2f58905fac06
-- title:
--   Theorem B.6.1.7 — slow growth near the poles of $1/L_{\Sigma_F-S}(s,\chi)$, I
-- statement:
--   Let $F$ be a number field and $\chi\colon C_F\to U(1)$ a Hecke character. For a finite place $v$ let $\mathfrak p_v$ be its prime ideal, $q_v=N(\mathfrak p_v)$ its norm, and $\chi(\mathfrak p_v)=\chi_v(\pi_v)$ the value of $\chi$ at a uniformizer if $\chi$ is unramified at $v$ (and $0$ otherwise). $L_f(s,\chi)$ is the finite Hecke $L$-function, continued meromorphically to $\mathbb C$.
--
--   Let $S$ be a finite set of places of $F$ containing the Archimedean places, with finite part $S_f$, and let
--   $$L_{\Sigma_F-S}(s,\chi)=L_f(s,\chi)\prod_{v\in S_f}\big(1-\chi(\mathfrak p_v)q_v^{-s}\big)$$
--   be the partial Hecke $L$-function. Then there is a real number $A>0$ such that:
--
--   1. for all sufficiently large $T$ the interval $(T,T+1)$ contains a real number $t$ with
--   $$|L_{\Sigma_F-S}(\sigma+it,\chi)|>|t|^{-A}\qquad\text{for all }-1\le\sigma\le2 ;$$
--   2. there is $T_0$ such that for every real $B>1$ and every $T\ge T_0$ there is a set $E\subset[T,T+1]$ of Lebesgue measure at most $1/B$ with
--   $$|L_{\Sigma_F-S}(\sigma+it,\chi)|>T^{-AB}\qquad\text{for all }t\in[T,T+1]\setminus E\text{ and all }-1\le\sigma\le2 .$$
--
--   The theorem provides horizontal lines, in every unit interval of large ordinates, on which $1/L_{\Sigma_F-S}(s,\chi)$ is polynomially bounded across the strip $-1\le\operatorname{Re}(s)\le2$.
--
--   **Formalization Note** The exceptional set of measure $1/B$ of the source is stated as a set of measure at most $1/B$; since $B>1$ and the interval has length $1$, the two forms are equivalent.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix B, §B.6.1.3, Theorem B.6.1.7 (Slow growth near the poles of 1/L_{Σ_F−S}(χ,s) - I), eqs. (B.6.1.35)–(B.6.1.36), pp. 641–642

import Definitions.Def_MasulloGRH_IdeleNorm

set_option autoImplicit false

namespace MasulloGRH

open NumberField IsDedekindDomain

theorem partialHeckeLFunction_lower_bound_on_short_intervals
    (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F)
    (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ A : ℝ, 0 < A ∧
      (∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∃ t ∈ Set.Ioo T (T + 1), ∀ σ ∈ Set.Icc (-1 : ℝ) 2,
        |t| ^ (-A) < ‖partialHeckeLFunction χ Sf (σ + t * Complex.I)‖) ∧
      (∃ T₀ : ℝ, ∀ B : ℝ, 1 < B → ∀ T : ℝ, T₀ ≤ T → ∃ E : Set ℝ, E ⊆ Set.Icc T (T + 1) ∧
        MeasureTheory.volume E ≤ ENNReal.ofReal (1 / B) ∧
        ∀ t ∈ Set.Icc T (T + 1) \ E, ∀ σ ∈ Set.Icc (-1 : ℝ) 2,
          T ^ (-(A * B)) < ‖partialHeckeLFunction χ Sf (σ + t * Complex.I)‖) := by sorry

end MasulloGRH
