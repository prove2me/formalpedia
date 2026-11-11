-- Prove2me | Theorems.Thm_MarginMaxima_Critical_lemma_5_6
-- name    : MarginMaxima.Critical.lemma_5_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:02:53.948217+00:00
-- url     : https://prove2.me/theorems/7731f7c5-4e55-40ee-ad71-744ab496579b
-- title:
--   Lemma 5.6 — Frobenius degree: $\rho=\sum_{s\in R}c_sx^s$ that is $\mathbb F_q$-valued at more than $D$ points lies in $G$
-- statement:
--   In the setting of §5.1, let $\rho=\sum_{s\in R}c_sx^s$ with $c_s\in K$. If $\rho(x)\in\mathbb F_q$ for more than $D=q^{u-1}+2q^{u-k-2}$ elements $x\in K$, then $\rho\in G$.
--
--   Differences from the source:
--   - encoding: q ≥ 3 a prime power, K = F_{q^u}, F_q ⊆ K → finite fields F, K with Algebra F K, card F = q ≥ 3, card K = q^u; F_q = image of F (Fq F K); reason: every field of order q^u is isomorphic to F_{q^u} and contains a unique copy of F_q; card F = q makes q a prime power
--   - encoding: polynomials of degree < N identified with their functions on K; V, E, G spaces of such functions → V, E as K-submodules of K[X] spanned by monomials, G as the F-submodule of K[X] of F_q-valued elements of span{X^s : s ∈ R}; reason: the paper's convention (p. 10): such a polynomial is determined by its function on K, so the spaces and dimensions agree
--   - encoding: ρ(x) ∈ F_q for more than D elements x ∈ K; D = max R → D < {x : K | eval x ρ ∈ Fq F K}.ncard; D = Dval = q^{u−1} + 2q^{u−k−2}; reason: the paper's own value of max R (p. 10)
-- source:
--   Tianlang Chen, The Margin Complexity of Maxima of Linear Functionals, STOC 2027 submission (manuscript sha256 dbfb896a…3901), p. 10, Lemma 5.6

import Mathlib
import Definitions.Def_MarginMaxima_Critical_ReedSolomon

open Polynomial

namespace MarginMaxima.Critical

theorem lemma_5_6 {F K : Type} [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]
    (q k u : ℕ) (hq : 3 ≤ q) (hF : Fintype.card F = q) (hK : Fintype.card K = q ^ u)
    (hk : 4 ≤ k) (hu : 2 * k + 5 ≤ u) (c : ℕ → K)
    (hD : Dval q k u <
      {x : K | (∑ s ∈ Rset q k u, C (c s) * X ^ s).eval x ∈ Fq F K}.ncard) :
    (∑ s ∈ Rset q k u, C (c s) * X ^ s) ∈ Gsp F K q k u := by sorry

end MarginMaxima.Critical
