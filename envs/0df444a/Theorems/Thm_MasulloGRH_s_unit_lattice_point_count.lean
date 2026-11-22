-- Prove2me | Theorems.Thm_MasulloGRH_s_unit_lattice_point_count
-- name    : MasulloGRH.s_unit_lattice_point_count
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-21T03:38:26.971198+00:00
-- url     : https://prove2.me/theorems/07b33db6-d7d5-4c22-9b21-615ee3c49e64
-- title:
--   Theorem A.4.1.1 — counting $S$-units in a box: $\sum_{\xi\in\mathcal O_{F,S}^\times}u(\xi g)\le C\,|\log|g|_{F,S}|^{|S|-1}$
-- statement:
--   Let $F$ be a number field and $S$ a finite set of places of $F$ containing the Archimedean places. Let $\mathbb A_{F,S}=\prod_{v\in S}F_v$, let $\mathcal O_{F,S}^\times$ be the group of $S$-units, embedded diagonally, and $|g|_{F,S}=\prod_{v\in S}|g_v|_v$ the $S$-idelic norm. Let $u$ be the indicator function of the box
--   $$\{x\in\mathbb A_{F,S}:\ |x_v|_v\le1\text{ for }v\mid\infty,\ x_v\in\mathcal O_{F_v}\text{ for }v\in S_f\}.$$
--
--   Then there are real numbers $C>0$ and $\varepsilon>0$ such that for every $S$-idele $g$ with $|g|_{F,S}<\varepsilon$,
--
--   $$\sum_{\xi\in\mathcal O_{F,S}^\times}u(\xi g)\ \le\ C\,\big|\log|g|_{F,S}\big|^{|S|-1}.$$
--
--   The sum counts the $S$-units $\xi$ with $\xi g$ in the box. The estimate controls the growth of the $S$-local $\theta$-functions as $|g|_{F,S}\to0^+$.
--
--   **Formalization Note** The sum is the cardinality of the set of $S$-units $\xi$ with $\xi g$ in the box; the statement asserts that this set is finite and bounds its cardinality. $|S|=r_1+r_2+|S_f|$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix A, §A.4.1, Theorem A.4.1.1 (Estimates on point-counting functions of the lattice of S-units), eqs. (A.4.1.1)–(A.4.1.3), p. 562

import Definitions.Def_MasulloGRH_SAdeles

set_option autoImplicit false

namespace MasulloGRH

open NumberField IsDedekindDomain

theorem s_unit_lattice_point_count (F : Type*) [Field F] [NumberField F]
    (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ g : SIdeleGroup F Sf, sIdeleNorm Sf g < ε →
      {ξ : Fˣ | ξ ∈ SUnits Sf ∧
        (∀ w : InfinitePlace F, ‖(sDiagonal Sf (ξ : F) * (g : SAdeleRing F Sf)).1 w‖ ≤ 1) ∧
        ∀ v : Sf, (sDiagonal Sf (ξ : F) * (g : SAdeleRing F Sf)).2 v ∈
          (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F}.Finite ∧
      (({ξ : Fˣ | ξ ∈ SUnits Sf ∧
        (∀ w : InfinitePlace F, ‖(sDiagonal Sf (ξ : F) * (g : SAdeleRing F Sf)).1 w‖ ≤ 1) ∧
        ∀ v : Sf, (sDiagonal Sf (ξ : F) * (g : SAdeleRing F Sf)).2 v ∈
          (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F}.ncard : ℝ) ≤
        C * |Real.log (sIdeleNorm Sf g)| ^
          (InfinitePlace.nrRealPlaces F + InfinitePlace.nrComplexPlaces F + Sf.card - 1)) := by sorry

end MasulloGRH
