-- Prove2me | Theorems.Thm_MasulloGRH_sLocalTheta_estimates
-- name    : MasulloGRH.sLocalTheta_estimates
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-21T04:36:06.789205+00:00
-- url     : https://prove2.me/theorems/67c2953e-e9bf-4742-ad63-0424c80d13ad
-- title:
--   Proposition 2.3.1.2 — convergence of $\Phi_{F,S}(f)$ and its decay as $|g|_{F,S}\to\infty$
-- statement:
--   Let $F$ be a number field and $S$ a finite set of places containing the Archimedean places. Let $\mathbb A_{F,S}=\prod_{v\in S}F_v$, $\mathcal S(\mathbb A_{F,S})$ its Schwartz–Bruhat space, $\mathcal O_{F,S}^\times$ the group of $S$-units and $|g|_{F,S}=\prod_{v\in S}|g_v|_v$ the $S$-idelic norm. For $f\in\mathcal S(\mathbb A_{F,S})$ the **$S$-local adelic $\theta$-function** is $\Phi_{F,S}(f)(g)=\sum_{\xi\in\mathcal O_{F,S}^\times}f(\xi g)$, $g\in\mathrm{GL}_1(\mathbb A_{F,S})$.
--
--   1. For every $f\in\mathcal S(\mathbb A_{F,S})$ the series defining $\Phi_{F,S}(f)(g)$ converges absolutely for every $g$, and uniformly on every compact subset of $\mathrm{GL}_1(\mathbb A_{F,S})$. The function $\Phi_{F,S}(f)$ is continuous and invariant under translation by $S$-units.
--   2. For every bounded subset $B\subset\mathcal S(\mathbb A_{F,S})$ and every integer $N\ge0$ there is a constant $C>0$ such that
--   $$|\Phi_{F,S}(f)(g)|\le C\,|g|_{F,S}^{-N}\qquad\text{for all }f\in B\text{ and all }g\text{ with }|g|_{F,S}>1 .$$
--
--   So the $S$-local $\theta$-functions are well defined and decay faster than every power of $|g|_{F,S}^{-1}$ at infinity, uniformly on bounded sets of test functions.
--
--   **Formalization Note** Item 2 is the uniform form of parts (3)–(4) of the source with threshold $1$; it contains part (2). Uniform convergence on a compact set is convergence of the net of finite partial sums.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Chapter 2, §2.3.1.1, Proposition 2.3.1.2 (Estimates over the S-idele classes - I), eq. (2.3.1.3), p. 100

import Definitions.Def_MasulloGRH_SLocalTheta

set_option autoImplicit false

namespace MasulloGRH

open NumberField IsDedekindDomain

theorem sLocalTheta_estimates (F : Type*) [Field F] [NumberField F]
    (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    (∀ f : SAdelicSchwartz F Sf,
      (∀ g : SIdeleGroup F Sf, Summable (fun ξ : SUnits Sf =>
        ‖f.eval (sDiagonal Sf ((ξ : Fˣ) : F) * (g : SAdeleRing F Sf))‖)) ∧
      (∀ K : Set (SIdeleGroup F Sf), IsCompact K → TendstoUniformlyOn
        (fun (s : Finset (SUnits Sf)) (g : SIdeleGroup F Sf) =>
          ∑ ξ ∈ s, f.eval (sDiagonal Sf ((ξ : Fˣ) : F) * (g : SAdeleRing F Sf)))
        (sLocalTheta f) Filter.atTop K) ∧
      Continuous (sLocalTheta f) ∧
      ∀ η ∈ SUnits Sf, ∀ g : SIdeleGroup F Sf,
        sLocalTheta f (Units.map (sDiagonal Sf).toMonoidHom η * g) = sLocalTheta f g) ∧
    (∀ B : Set (SAdelicSchwartz F Sf), Bornology.IsVonNBounded ℂ B → ∀ N : ℕ,
      ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : SIdeleGroup F Sf, 1 < sIdeleNorm Sf g →
        ‖sLocalTheta f g‖ ≤ C * sIdeleNorm Sf g ^ (-(N : ℤ))) := by sorry

end MasulloGRH
