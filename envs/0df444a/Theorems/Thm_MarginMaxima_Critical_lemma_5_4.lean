-- Prove2me | Theorems.Thm_MarginMaxima_Critical_lemma_5_4
-- name    : MarginMaxima.Critical.lemma_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:02:41.165615+00:00
-- url     : https://prove2.me/theorems/13b42831-b24c-4d61-9d00-90d1ec0fc162
-- title:
--   Lemma 5.4 — dimension of the multiplier code: $u\lfloor(u-1-2k)/2\rfloor\le\tau\le|R|\le2a$
-- statement:
--   In the setting of §5.1, let $f(u)=u\lfloor(u-1-2k)/2\rfloor$. Then
--   $$f(u)\le\tau\le|R|\le 2a,$$
--   where $\tau=\dim_{\mathbb F_q}G$.
--
--   Differences from the source:
--   - encoding: q ≥ 3 a prime power, K = F_{q^u}, F_q ⊆ K → finite fields F, K with Algebra F K, card F = q ≥ 3, card K = q^u; F_q = image of F (Fq F K); reason: every field of order q^u is isomorphic to F_{q^u} and contains a unique copy of F_q; card F = q makes q a prime power
--   - encoding: polynomials of degree < N identified with their functions on K; V, E, G spaces of such functions → V, E as K-submodules of K[X] spanned by monomials, G as the F-submodule of K[X] of F_q-valued elements of span{X^s : s ∈ R}; reason: the paper's convention (p. 10): such a polynomial is determined by its function on K, so the spaces and dimensions agree
--   - encoding: ⌊(u − 1 − 2k)/2⌋, τ = dim_{F_q} G → ℕ division (u − 1 − 2k)/2 (u ≥ 2k + 5, so no truncation), tauRS = Module.finrank F (Gsp F K q k u); reason: literal
-- source:
--   Tianlang Chen, The Margin Complexity of Maxima of Linear Functionals, STOC 2027 submission (manuscript sha256 dbfb896a…3901), p. 10, Lemma 5.4

import Mathlib
import Definitions.Def_MarginMaxima_Critical_ReedSolomon

open Polynomial

namespace MarginMaxima.Critical

theorem lemma_5_4 {F K : Type} [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]
    (q k u : ℕ) (hq : 3 ≤ q) (hF : Fintype.card F = q) (hK : Fintype.card K = q ^ u)
    (hk : 4 ≤ k) (hu : 2 * k + 5 ≤ u) :
    u * ((u - 1 - 2 * k) / 2) ≤ tauRS F K q k u ∧ tauRS F K q k u ≤ (Rset q k u).card ∧
      (Rset q k u).card ≤ 2 * aRS q k u := by sorry

end MarginMaxima.Critical
