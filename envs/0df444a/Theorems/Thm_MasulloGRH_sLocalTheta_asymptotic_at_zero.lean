-- Prove2me | Theorems.Thm_MasulloGRH_sLocalTheta_asymptotic_at_zero
-- name    : MasulloGRH.sLocalTheta_asymptotic_at_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-21T04:36:33.319859+00:00
-- url     : https://prove2.me/theorems/d312e628-f4f6-4cf0-834f-9b84aa3c0cb0
-- title:
--   Theorem 2.4.2.1 — growth of the $S$-local $\theta$-functions as $|g|_{F,S}\to0^+$: $|\Phi_{F,S}(f)(g)|\le C_1|\log|g|_{F,S}|^{|S|-1}+C_2$
-- statement:
--   Let $F$ be a number field and $S$ a finite set of places containing the Archimedean places. Let $\mathbb A_{F,S}=\prod_{v\in S}F_v$, $\mathcal S(\mathbb A_{F,S})$ its Schwartz–Bruhat space, $\mathcal O_{F,S}^\times$ the group of $S$-units and $|g|_{F,S}=\prod_{v\in S}|g_v|_v$ the $S$-idelic norm. For $f\in\mathcal S(\mathbb A_{F,S})$ the **$S$-local adelic $\theta$-function** is $\Phi_{F,S}(f)(g)=\sum_{\xi\in\mathcal O_{F,S}^\times}f(\xi g)$, $g\in\mathrm{GL}_1(\mathbb A_{F,S})$.
--
--   Let $B\subset\mathcal S(\mathbb A_{F,S})$ be a bounded subset. Then there are real numbers $C_1,C_2>0$ such that for every $f\in B$ and every $S$-idele $g$ with $|g|_{F,S}<1$
--
--   $$|\Phi_{F,S}(f)(g)|\le C_1\,\big|\log|g|_{F,S}\big|^{|S|-1}+C_2 .$$
--
--   Unlike the global $\theta$-functions, the $S$-local ones do not have an asymptotic expansion in powers of $|g|_{F,S}$ at $0$; they grow at most like a power of the logarithm, the power being the rank $|S|-1$ of the group of $S$-units.
--
--   **Formalization Note** $|S|=r_1+r_2+|S_f|$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Chapter 2, §2.4.2, Theorem 2.4.2.1 (On the asymptotic behavior of the S-local θ-functions as |g|_{F,S} → 0+), eq. (2.4.2.1), p. 111

import Definitions.Def_MasulloGRH_SLocalTheta

set_option autoImplicit false

namespace MasulloGRH

open NumberField IsDedekindDomain

theorem sLocalTheta_asymptotic_at_zero (F : Type*) [Field F] [NumberField F]
    (Sf : Finset (HeightOneSpectrum (𝓞 F))) (B : Set (SAdelicSchwartz F Sf))
    (hB : Bornology.IsVonNBounded ℂ B) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ f ∈ B, ∀ g : SIdeleGroup F Sf, sIdeleNorm Sf g < 1 →
      ‖sLocalTheta f g‖ ≤
        C₁ * |Real.log (sIdeleNorm Sf g)| ^
          (InfinitePlace.nrRealPlaces F + InfinitePlace.nrComplexPlaces F + Sf.card - 1) + C₂ := by sorry

end MasulloGRH
