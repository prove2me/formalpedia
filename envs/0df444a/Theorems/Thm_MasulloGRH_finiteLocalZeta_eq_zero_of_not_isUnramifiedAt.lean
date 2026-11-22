-- Prove2me | Theorems.Thm_MasulloGRH_finiteLocalZeta_eq_zero_of_not_isUnramifiedAt
-- name    : MasulloGRH.finiteLocalZeta_eq_zero_of_not_isUnramifiedAt
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:35:00.867115+00:00
-- url     : https://prove2.me/theorems/17d3afc5-f557-482f-a4b1-418cba8b7dc2
-- title:
--   p. 302 — if $\chi$ is ramified at $v$, then $Z_v(f,\chi_v|\cdot|_v^s)=0$ for every $\mathcal O_{F_v}^\times$-invariant $f$ (e.g. $f=1_{\pi_v^N\mathcal O_{F_v}}$)
-- statement:
--   **Ramified local zeta integrals vanish on unit-invariant functions** (the step in the proof of Theorem 6.2.2.1(1) of the source, p. 302).
--
--   Let $F$ be a number field, $\chi$ a Hecke character of $F$, $v$ a finite place with completion $F_v$ and ring of integers $\mathcal O_{F_v}$, $|\cdot|_v$ the normalized absolute value, $\mu_v$ the local multiplicative Tamagawa measure on $F_v^\times$ (a Haar measure) and $\chi_v$ the local component of $\chi$ at $v$. Assume that $\chi$ is **ramified** at $v$, i.e. $\chi_v$ is not trivial on $\mathcal O_{F_v}^\times$. Let $f:F_v\to\mathbb C$ be invariant under the units: $f(ux)=f(x)$ for all $u\in\mathcal O_{F_v}^\times$ and $x\in F_v$. Then for every $s\in\mathbb C$
--   $$Z_v(f,\chi_v|\cdot|_v^s)=\int_{F_v^\times}f(x)\,\chi_v(x)\,|x|_v^s\,d\mu_v(x)=0 .$$
--
--   The source applies this to $f=1_{\pi_v^N\mathcal O_{F_v}}$, where $\pi_v$ is a uniformizer of $F_v$ and $N\ge0$: if a Schwartz–Bruhat function $g$ on $F_v$ is constant on $\pi_v^N\mathcal O_{F_v}$, then $g-g(0)\,1_{\pi_v^N\mathcal O_{F_v}}$ vanishes on a neighbourhood of $0$ and has the same zeta integral as $g$ against a ramified character, so at ramified places every local zeta integral is entire in $s$ (the local Euler factor is $1$).
--
--   **Formalization Note.** $\chi_v$ is `HeckeCharacter.localComponent`, ramified means `¬ HeckeCharacter.IsUnramifiedAt`, $\mu_v$ is `MasulloGRH.finiteLocalMulTamagawa` and $|x|_v$ the norm of `v.adicCompletion F`. No integrability hypothesis is imposed: when the integrand is not integrable the Bochner integral is $0$ by convention, so the statement has content exactly for those $f$ and $s$ for which the integral converges absolutely. Units of $\mathcal O_{F_v}$ are the elements of valuation $1$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 302, proof of Theorem 6.2.2.1(1) (the identity $Z_v(1_{\pi_v^N\mathcal O_{F_v}},\chi_v|\cdot|_v^s)=0$ for $\chi_v|_{\mathcal O_{F_v}^\times}\neq1$); local zeta integral (3.3.1.7), p. 130 (the paper refers to [CF, Ch. XV, Def. 2.4.1]), with $\mu_v$ the local multiplicative Tamagawa measure of Definition A.3.2.2, p. 560

import Mathlib
import Definitions.Def_MasulloGRH_HeckeLFunction
import Definitions.Def_MasulloGRH_SLocalTamagawaMeasures

open MeasureTheory NumberField IsDedekindDomain

set_option autoImplicit false

namespace MasulloGRH

theorem finiteLocalZeta_eq_zero_of_not_isUnramifiedAt
    (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (hχ : ¬ χ.IsUnramifiedAt v) (f : v.adicCompletion F → ℂ)
    (hf : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 →
      ∀ x : v.adicCompletion F, f (u * x) = f x)
    (s : ℂ) :
    ∫ x : (v.adicCompletion F)ˣ,
      f (x : v.adicCompletion F) * χ.localComponent v x *
        ((‖(x : v.adicCompletion F)‖ : ℝ) : ℂ) ^ s ∂(finiteLocalMulTamagawa F v) = 0 := by sorry

end MasulloGRH
