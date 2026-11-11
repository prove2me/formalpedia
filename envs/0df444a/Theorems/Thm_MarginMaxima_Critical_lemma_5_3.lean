-- Prove2me | Theorems.Thm_MarginMaxima_Critical_lemma_5_3
-- name    : MarginMaxima.Critical.lemma_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:02:52.231437+00:00
-- url     : https://prove2.me/theorems/b1ae6c39-ab30-4cee-9055-9c6e3e19bb82
-- title:
--   Lemma 5.3 — the exponent sets: $T_0$, $T_p$ are separated intervals; $(k+1)a\le\dim_KE=|T|\le(k+2)a$, $\max T+a-1<N$; $|R|\le2a$
-- statement:
--   In the setting of §5.1 ($q\ge3$ a prime power, $k\ge4$, $u\ge2k+5$):
--
--   (i) $T_0$ and the $T_p$ are integer intervals, pairwise separated by a nonempty gap.
--
--   (ii) $(k+1)a\le\dim_KE=|T|\le(k+2)a$, and $\max T+a-1<N$.
--
--   (iii) $|R|\le 2a$.
--
--   Differences from the source:
--   - encoding: q ≥ 3 a prime power, K = F_{q^u}, F_q ⊆ K → finite fields F, K with Algebra F K, card F = q ≥ 3, card K = q^u; F_q = image of F (Fq F K); reason: every field of order q^u is isomorphic to F_{q^u} and contains a unique copy of F_q; card F = q makes q a prime power
--   - encoding: polynomials of degree < N identified with their functions on K; V, E, G spaces of such functions → V, E as K-submodules of K[X] spanned by monomials, G as the F-submodule of K[X] of F_q-valued elements of span{X^s : s ∈ R}; reason: the paper's convention (p. 10): such a polynomial is determined by its function on K, so the spaces and dimensions agree
--   - encoding: T₀ and T_p (u − k < p ≤ u − 1) are integer intervals pairwise separated by a nonempty gap → Tcomp p for p ∈ [u − k, u − 1] (p = u − k is T₀) equals Finset.Icc lo hi, and elements x, y of distinct components satisfy x + 1 < y ∨ y + 1 < x; reason: for intervals, being at distance at least 2 elementwise is exactly separation by a nonempty gap
--   - encoding: max T + a − 1 < N → ∀ b ∈ T, b + a − 1 < q^u; reason: T is nonempty, so this is the bound on its maximum; a ≥ 1 so ℕ subtraction is exact
-- source:
--   Tianlang Chen, The Margin Complexity of Maxima of Linear Functionals, STOC 2027 submission (manuscript sha256 dbfb896a…3901), p. 10, Lemma 5.3

import Mathlib
import Definitions.Def_MarginMaxima_Critical_ReedSolomon

open Polynomial

namespace MarginMaxima.Critical

theorem lemma_5_3 {F K : Type} [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]
    (q k u : ℕ) (hq : 3 ≤ q) (hF : Fintype.card F = q) (hK : Fintype.card K = q ^ u)
    (hk : 4 ≤ k) (hu : 2 * k + 5 ≤ u) :
    ((∀ p ∈ Finset.Icc (u - k) (u - 1), ∃ lo hi : ℕ, Tcomp q k u p = Finset.Icc lo hi) ∧
      (∀ p ∈ Finset.Icc (u - k) (u - 1), ∀ p' ∈ Finset.Icc (u - k) (u - 1), p ≠ p' →
        ∀ x ∈ Tcomp q k u p, ∀ y ∈ Tcomp q k u p', x + 1 < y ∨ y + 1 < x)) ∧
    ((k + 1) * aRS q k u ≤ Module.finrank K (Esp K q k u) ∧
      Module.finrank K (Esp K q k u) = (Tset q k u).card ∧
      (Tset q k u).card ≤ (k + 2) * aRS q k u ∧
      ∀ b ∈ Tset q k u, b + aRS q k u - 1 < q ^ u) ∧
    (Rset q k u).card ≤ 2 * aRS q k u := by sorry

end MarginMaxima.Critical
