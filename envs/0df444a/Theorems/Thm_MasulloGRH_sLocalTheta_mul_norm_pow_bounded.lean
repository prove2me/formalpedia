-- Prove2me | Theorems.Thm_MasulloGRH_sLocalTheta_mul_norm_pow_bounded
-- name    : MasulloGRH.sLocalTheta_mul_norm_pow_bounded
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-21T04:36:56.425117+00:00
-- url     : https://prove2.me/theorems/3f062949-9713-48c6-a1bd-7e0d5aaa5ae1
-- title:
--   Proposition 2.4.3.1 — $\Phi_{F,S}(f)(g)\,|g|_{F,S}^{\varepsilon}$ is bounded as $|g|_{F,S}\to0^+$
-- statement:
--   Let $F$ be a number field and $S$ a finite set of places containing the Archimedean places. Let $\mathbb A_{F,S}=\prod_{v\in S}F_v$, $\mathcal S(\mathbb A_{F,S})$ its Schwartz–Bruhat space, $\mathcal O_{F,S}^\times$ the group of $S$-units and $|g|_{F,S}=\prod_{v\in S}|g_v|_v$ the $S$-idelic norm. For $f\in\mathcal S(\mathbb A_{F,S})$ the **$S$-local adelic $\theta$-function** is $\Phi_{F,S}(f)(g)=\sum_{\xi\in\mathcal O_{F,S}^\times}f(\xi g)$, $g\in\mathrm{GL}_1(\mathbb A_{F,S})$.
--
--   Let $B\subset\mathcal S(\mathbb A_{F,S})$ be a bounded subset and $\varepsilon>0$. Then there is a real number $C$ such that
--
--   $$|\Phi_{F,S}(f)(g)|\cdot|g|_{F,S}^{\varepsilon}\le C\qquad\text{for all }f\in B\text{ and all }g\text{ with }|g|_{F,S}<1 .$$
--
--   The bound says that $\Phi_{F,S}(f)$ grows more slowly than every negative power of $|g|_{F,S}$ at $0$, so that its Mellin transform converges for every quasi-character of positive abscissa.
--
--   **Formalization Note** The statement concerns $\Phi_{F,S}$ only, in the uniform form of part (3) of the source.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Chapter 2, §2.4.3, Proposition 2.4.3.1, eq. (2.4.3.1), p. 113, for Φ_{F,S} in the uniform form of part (3)

import Definitions.Def_MasulloGRH_SLocalTheta

set_option autoImplicit false

namespace MasulloGRH

open NumberField IsDedekindDomain

theorem sLocalTheta_mul_norm_pow_bounded (F : Type*) [Field F] [NumberField F]
    (Sf : Finset (HeightOneSpectrum (𝓞 F))) (B : Set (SAdelicSchwartz F Sf))
    (hB : Bornology.IsVonNBounded ℂ B) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ f ∈ B, ∀ g : SIdeleGroup F Sf, sIdeleNorm Sf g < 1 →
      ‖sLocalTheta f g‖ * sIdeleNorm Sf g ^ ε ≤ C := by sorry

end MasulloGRH
