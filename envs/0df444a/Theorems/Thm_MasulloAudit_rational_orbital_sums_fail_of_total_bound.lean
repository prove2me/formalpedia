-- Prove2me | Theorems.Thm_MasulloAudit_rational_orbital_sums_fail_of_total_bound
-- name    : MasulloAudit.rational_orbital_sums_fail_of_total_bound
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T02:03:21.911438+00:00
-- url     : https://prove2.me/theorems/7c857037-9daf-4033-a845-5514fd437231
-- title:
--   Pointwise escape of rational adelic Schwartz–Bruhat tests with fixed absolute orbital sums
-- statement:
--   There are Schwartz–Bruhat functions $f_n$ on $\mathbb A_{\mathbb Q}$ and a function $B$ on the rational ideles with $B(1)\ge1$. For every adele $x$, $f_n(x)$ is eventually zero. Nevertheless, for every idele $g$ and every $n$,
--   $$\sum_{q\in\mathbb Q^\times}|f_n(qg)|=B(g),\qquad \sum_{q\in\mathbb Q^\times}f_n(qg)=B(g).$$
--   Both series converge. This contradicts the pointwise conclusion (11.1.1.10) of Corollary 11.1.1.4. For its bound (11.1.1.8), one can take $I_g=\mathbb Z$ and put mass $B(g)$ at the summation index $1$. Thus even equality in the total orbit bound allows mass to escape along the orbit.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen 20 November 2026 draft, Chapter 11, Corollary 11.1.1.4, p. 478, equations (11.1.1.8)–(11.1.1.10). https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Definitions.Def_NumberField_AdelicFourier

open NumberField Filter Topology

theorem MasulloAudit.rational_orbital_sums_fail_of_total_bound :
    ∃ (f : ℕ → AdeleRing (𝓞 ℚ) ℚ → ℂ) (B : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℝ),
      (∀ n, f n∈AdelicFourier.schwartzBruhat ℚ) ∧
      (∀ x,∀ᶠ n : ℕ in atTop,f n x=0) ∧ 1≤B 1 ∧
      ∀ (g : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (n : ℕ),
        HasSum (fun q : ℚˣ => ‖f n (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (q:ℚ)*g)‖) (B g) ∧
        HasSum (fun q : ℚˣ => f n (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (q:ℚ)*g)) (B g:ℂ) := by sorry
