-- Prove2me | Theorems.Thm_MasulloGRH_finiteLocalZeta_integers_of_unramified
-- name    : MasulloGRH.finiteLocalZeta_integers_of_unramified
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:23:32.861243+00:00
-- url     : https://prove2.me/theorems/e9ad9adb-cb05-415b-aa81-6b377a606f45
-- title:
--   Unramified local zeta integral (proof of Theorem 3.4.1.1): $\int_{\mathcal O_{F_v}\setminus\{0\}}c\,d\mu_v=N(\mathfrak d_v)^{-1/2}\,(1-c(\pi_v))^{-1}$
-- statement:
--   **The unramified computation: the local zeta integral of $1_{\mathcal O_{F_v}}$ is the local Euler factor** (computation in the proof of Theorem 3.4.1.1 of the source, p. 144; Tate's unramified local computation).
--
--   Let $F$ be a number field, $v$ a finite place, $F_v$ the completion, $\mathcal O_{F_v}$ its ring of integers, $\pi_v$ a uniformizer, and $\mu_v$ the local multiplicative Tamagawa measure on $F_v^\times$ (the Haar measure with $\mu_v(\mathcal O_{F_v}^\times)=N(\mathfrak d_v)^{-1/2}$, $\mathfrak d_v$ the local different). Let $c:F_v^\times\to\mathbb C$ be multiplicative and *unramified*, i.e. $c(u)=1$ for all units $u\in\mathcal O_{F_v}^\times$, with $|c(\pi_v)|<1$ (for a quasi-character $c=\chi_v|\cdot|_v^s$ with $\chi_v$ unitary and unramified this means $\operatorname{Re}s>0$).
--
--   Then $c$ is $\mu_v$-integrable on $\mathcal O_{F_v}\setminus\{0\}$ and
--   $$Z_v(1_{\mathcal O_{F_v}},c)=\int_{\mathcal O_{F_v}\setminus\{0\}}c(x)\,d\mu_v(x)=N(\mathfrak d_v)^{-1/2}\,\frac1{1-c(\pi_v)}.$$
--
--   For $c=\chi_v|\cdot|_v^s$ the right side is $\mu_v(\mathcal O_{F_v}^\times)\,(1-\chi(\mathfrak p_v)N(\mathfrak p_v)^{-s})^{-1}$: the local zeta integral of the standard function is the local factor of the Hecke $L$-function, up to the volume of the units. This is the local input of the Euler factorization of the global zeta integral (Weil's identity, Theorem 3.4.1.1), and of the definition of the local $L$-factors $L_v(c_v)$.
--
--   **Formalization Note.** $\mathcal O_{F_v}\setminus\{0\}$ is the set of $x\in F_v^\times$ of valuation $\le1$; a uniformizer is an element of valuation $\exp(-1)$ in $\mathbb Z^{m0}$ (`IsUniformizerAt`). $N(\mathfrak d_v)=N(\mathfrak p_v)^{m_v}$ with $m_v$ the multiplicity of $\mathfrak p_v$ in the different of $F/\mathbb Q$. Continuity of $c$ is automatic for an unramified multiplicative function and is not assumed.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 144, proof of Theorem 3.4.1.1 (the two displayed computations); p. 127, Example 3.2.2.4; normalization of $\mu_v$: p. 560, Definition A.3.2.2

import Mathlib
import Definitions.Def_MasulloGRH_SLocalTamagawaMeasures

open MeasureTheory NumberField IsDedekindDomain

set_option autoImplicit false

namespace MasulloGRH

theorem finiteLocalZeta_integers_of_unramified
    (F : Type*) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (c : (v.adicCompletion F)ˣ → ℂ)
    (hmul : ∀ x y : (v.adicCompletion F)ˣ, c (x * y) = c x * c y)
    (hunr : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → c u = 1)
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : IsUniformizerAt v ϖ) (hσ : ‖c ϖ‖ < 1) :
    IntegrableOn c {x : (v.adicCompletion F)ˣ | Valued.v (x : v.adicCompletion F) ≤ 1}
      (finiteLocalMulTamagawa F v) ∧
    ∫ x in {x : (v.adicCompletion F)ˣ | Valued.v (x : v.adicCompletion F) ≤ 1}, c x
        ∂(finiteLocalMulTamagawa F v) =
      (((Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
        multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))))⁻¹ : ℝ) : ℂ) * (1 - c ϖ)⁻¹ := by sorry

end MasulloGRH
