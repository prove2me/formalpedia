-- Prove2me | Theorems.Thm_MarginMaxima_Critical_lemma_5_5
-- name    : MarginMaxima.Critical.lemma_5_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:02:52.979854+00:00
-- url     : https://prove2.me/theorems/bdb411b3-9170-4f84-9680-e990d4e32438
-- title:
--   Lemma 5.5 — multiplication: $GV\subseteq E$, and a rational function $\rho$ with $\rho V\subseteq E$ has exponents in $R$
-- statement:
--   In the setting of §5.1: $\phi v\in E$ for $\phi\in G$, $v\in V$. If $\rho$ is a rational function over $K$ with $\rho V\subseteq E$, then $\rho=\sum_{s\in R}c_sx^s$ for some $c_s\in K$.
--
--   Differences from the source:
--   - encoding: q ≥ 3 a prime power, K = F_{q^u}, F_q ⊆ K → finite fields F, K with Algebra F K, card F = q ≥ 3, card K = q^u; F_q = image of F (Fq F K); reason: every field of order q^u is isomorphic to F_{q^u} and contains a unique copy of F_q; card F = q makes q a prime power
--   - encoding: polynomials of degree < N identified with their functions on K; V, E, G spaces of such functions → V, E as K-submodules of K[X] spanned by monomials, G as the F-submodule of K[X] of F_q-valued elements of span{X^s : s ∈ R}; reason: the paper's convention (p. 10): such a polynomial is determined by its function on K, so the spaces and dimensions agree
--   - encoding: ρ a rational function over K with ρV ⊆ E; ρ = Σ_{s∈R} c_s x^s → ρ : RatFunc K such that for every v ∈ V some w ∈ E has ρ·v = w in RatFunc K; ∃ c : ℕ → K with ρ = Σ_{s∈R} C (c s) X^s in RatFunc K; reason: rational functions are RatFunc K, polynomials embedded by algebraMap
-- source:
--   Tianlang Chen, The Margin Complexity of Maxima of Linear Functionals, STOC 2027 submission (manuscript sha256 dbfb896a…3901), p. 10, Lemma 5.5

import Mathlib
import Definitions.Def_MarginMaxima_Critical_ReedSolomon

open Polynomial

namespace MarginMaxima.Critical

theorem lemma_5_5 {F K : Type} [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]
    (q k u : ℕ) (hq : 3 ≤ q) (hF : Fintype.card F = q) (hK : Fintype.card K = q ^ u)
    (hk : 4 ≤ k) (hu : 2 * k + 5 ≤ u) :
    (∀ ϕ ∈ Gsp F K q k u, ∀ v ∈ Vsp K q k u, ϕ * v ∈ Esp K q k u) ∧
    ∀ ρ : RatFunc K,
      (∀ v ∈ Vsp K q k u, ∃ w ∈ Esp K q k u,
        ρ * algebraMap K[X] (RatFunc K) v = algebraMap K[X] (RatFunc K) w) →
      ∃ c : ℕ → K, ρ = algebraMap K[X] (RatFunc K) (∑ s ∈ Rset q k u, C (c s) * X ^ s) := by sorry

end MarginMaxima.Critical
