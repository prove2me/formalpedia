-- Prove2me | Theorems.Thm_MasulloGRH_sLocalTheta_mul_norm_pow_tendsto_zero
-- name    : MasulloGRH.sLocalTheta_mul_norm_pow_tendsto_zero
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-21T04:37:18.299185+00:00
-- url     : https://prove2.me/theorems/99ae27be-8b98-425d-90dc-0bb32f69900a
-- title:
--   Corollary 2.4.3.2 — $|g|_{F,S}^{\varepsilon}\,\Phi_{F,S}(f)(g)\to0$ as $|g|_{F,S}\to0^+$
-- statement:
--   Let $F$ be a number field and $S$ a finite set of places containing the Archimedean places. Let $\mathbb A_{F,S}=\prod_{v\in S}F_v$, $\mathcal S(\mathbb A_{F,S})$ its Schwartz–Bruhat space, $\mathcal O_{F,S}^\times$ the group of $S$-units and $|g|_{F,S}=\prod_{v\in S}|g_v|_v$ the $S$-idelic norm. For $f\in\mathcal S(\mathbb A_{F,S})$ the **$S$-local adelic $\theta$-function** is $\Phi_{F,S}(f)(g)=\sum_{\xi\in\mathcal O_{F,S}^\times}f(\xi g)$, $g\in\mathrm{GL}_1(\mathbb A_{F,S})$.
--
--   For every $f\in\mathcal S(\mathbb A_{F,S})$ and every real $\varepsilon>0$,
--
--   $$|g|_{F,S}^{\varepsilon}\,\Phi_{F,S}(f)(g)\longrightarrow0\qquad\text{as }|g|_{F,S}\to0^+ .$$
--
--   **Formalization Note** The limit is stated as: for every $\delta>0$ there is $T>0$ with $|g|_{F,S}^\varepsilon|\Phi_{F,S}(f)(g)|<\delta$ whenever $|g|_{F,S}<T$. The statement concerns $\Phi_{F,S}$ only.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Chapter 2, §2.4.3, Corollary 2.4.3.2, eq. (2.4.3.5), p. 115, for Φ_{F,S}

import Definitions.Def_MasulloGRH_SLocalTheta

set_option autoImplicit false

namespace MasulloGRH

open NumberField IsDedekindDomain

theorem sLocalTheta_mul_norm_pow_tendsto_zero (F : Type*) [Field F] [NumberField F]
    (Sf : Finset (HeightOneSpectrum (𝓞 F))) (f : SAdelicSchwartz F Sf) (ε : ℝ) (hε : 0 < ε) :
    ∀ δ : ℝ, 0 < δ → ∃ T : ℝ, 0 < T ∧ ∀ g : SIdeleGroup F Sf, sIdeleNorm Sf g < T →
      sIdeleNorm Sf g ^ ε * ‖sLocalTheta f g‖ < δ := by sorry

end MasulloGRH
