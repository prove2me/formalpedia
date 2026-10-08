-- Prove2me | Theorems.Thm_KonyaginUnitVectors_Alon_fourier_system
-- name    : KonyaginUnitVectors.Alon.fourier_system
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T14:26:33.943032+00:00
-- url     : https://prove2.me/theorems/9e1e9bcf-a203-4e27-acb2-db686f95f7a1
-- title:
--   A Fourier system of vectors with a prescribed Gram matrix
-- statement:
--   Throughout, $F$ is a finite field of characteristic $2$ with $q$ elements, regarded as an algebra over $\mathbb F_2$ (for example $\mathrm{GF}(2^k)$), $\mathrm{Tr}:F\to\mathbb F_2$ is the absolute trace, and $\psi(y)=(-1)^{\mathrm{Tr}(y)}\in\{1,-1\}$ is the associated additive character of $F$.
--
--   Let $S\subseteq F^3$ be any subset (the additive group $F^3$ has $n=q^3$ elements), let $\kappa\in\mathbb R$, and let $\chi_w(g)=\psi(w_1g_1+w_2g_2+w_3g_3)$ be the characters of $F^3$. Suppose
--
--   $$1+\kappa\sum_{s\in S}\chi_w(s)\ \ge\ 0\qquad\text{for every }w\in F^3 .$$
--
--   Then there are vectors $u_g\in\mathbb R^{F^3}$, $g\in F^3$, with
--
--   $$\langle u_g,u_h\rangle=[g=h]+\kappa\,[g+h\in S]\qquad(g,h\in F^3)$$
--
--   and
--
--   $$\Bigl\|\sum_{g}u_g\Bigr\|^{2}=q^{3}\bigl(1+\kappa\,|S|\bigr).$$
--
--   In other words, $I+\kappa A$ is the Gram matrix of a vector system whenever it is positive semidefinite, where $A$ is the adjacency matrix of the Cayley graph on $F^3$ with connection set $S$. This is the Fourier (spectral) realisation of orthonormal labelings from Cayley graphs used in Alon's construction.
--
--   **Formalization Note.** `chi F w s` is the character of the definition module `KonyaginUnitVectors_AlonConstruction`; the vectors live in `EuclideanSpace ℝ (F × F × F)` and `inner ℝ` is its inner product. No assumption such as $0\notin S$ is needed.
-- source:
--   N. Alon, Explicit Ramsey graphs and orthonormal labelings, Electron. J. Combin. 1 (1994), R12, doi:10.37236/1192 (Sections 3 and 4; the construction here partitions by Tr(x^9) instead of the leading bit of x^7)

import Mathlib
import Definitions.Def_KonyaginUnitVectors_AlonConstruction

namespace KonyaginUnitVectors.Alon

open Classical in
theorem fourier_system (F : Type*) [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
    (S : Finset (F × F × F)) (κ : ℝ)
    (hκ : ∀ w : F × F × F, 0 ≤ 1 + κ * ∑ s ∈ S, chi F w s) :
    ∃ u : F × F × F → EuclideanSpace ℝ (F × F × F),
      (∀ g h : F × F × F, inner ℝ (u g) (u h) = (if g = h then (1 : ℝ) else 0) + κ * (if g + h ∈ S then 1 else 0)) ∧
      ‖∑ g, u g‖ ^ 2 = (Fintype.card F : ℝ) ^ 3 * (1 + κ * (S.card : ℝ)) := by sorry

end KonyaginUnitVectors.Alon
