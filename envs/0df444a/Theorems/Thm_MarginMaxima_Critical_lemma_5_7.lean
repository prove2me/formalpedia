-- Prove2me | Theorems.Thm_MarginMaxima_Critical_lemma_5_7
-- name    : MarginMaxima.Critical.lemma_5_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:02:46.222426+00:00
-- url     : https://prove2.me/theorems/452e6434-59e2-49d4-9028-fb00ef932e6b
-- title:
--   Lemma 5.7 — Reed–Solomon lines: $A(y)=N$ on the line and $\le\theta N$ off it; lines with non-proportional spanning directions meet only at $x_0$
-- statement:
--   In the setting of §5.2 ($e\ge1$, $C=E^e$, $x_0\in C$, $\theta=1/q+3q^{-k}$):
--
--   (i) For spanning $h$, $A(y)=N$ on $B(x_0,h)$, and $A(y)\le\theta N$ for $y\in C$ off it.
--
--   (ii) If $h,h'$ are spanning and not proportional over $\mathbb F_q$, then $B(x_0,h)\cap B(x_0,h')=\{x_0\}$.
--
--   Differences from the source:
--   - encoding: q ≥ 3 a prime power, K = F_{q^u}, F_q ⊆ K → finite fields F, K with Algebra F K, card F = q ≥ 3, card K = q^u; F_q = image of F (Fq F K); reason: every field of order q^u is isomorphic to F_{q^u} and contains a unique copy of F_q; card F = q makes q a prime power
--   - encoding: polynomials of degree < N identified with their functions on K; V, E, G spaces of such functions → V, E as K-submodules of K[X] spanned by monomials, G as the F-submodule of K[X] of F_q-valued elements of span{X^s : s ∈ R}; reason: the paper's convention (p. 10): such a polynomial is determined by its function on K, so the spaces and dimensions agree
--   - encoding: C = E^e, x₀ ∈ C, y ∈ C → tuples Fin e → K[X] whose components lie in Esp; reason: literal
--   - encoding: h, h′ not proportional over F_q → ¬∃ c ∈ Fq F K, h′ = c • h; reason: spanning tuples are nonzero, so proportionality over F_q is symmetric
-- source:
--   Tianlang Chen, The Margin Complexity of Maxima of Linear Functionals, STOC 2027 submission (manuscript sha256 dbfb896a…3901), p. 11, Lemma 5.7

import Mathlib
import Definitions.Def_MarginMaxima_Critical_ReedSolomon

open Polynomial

namespace MarginMaxima.Critical

theorem lemma_5_7 {F K : Type} [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]
    (q k u : ℕ) (hq : 3 ≤ q) (hF : Fintype.card F = q) (hK : Fintype.card K = q ^ u)
    (hk : 4 ≤ k) (hu : 2 * k + 5 ≤ u) (e : ℕ) (he : 1 ≤ e)
    (x0 : Fin e → K[X]) (hx0 : ∀ i, x0 i ∈ Esp K q k u) :
    (∀ h : Fin e → K[X], IsSpanning K q k u h →
      (∀ y ∈ rsLine F K q k u x0 h, rsAgree F K x0 h y = q ^ u) ∧
      (∀ y : Fin e → K[X], (∀ i, y i ∈ Esp K q k u) → y ∉ rsLine F K q k u x0 h →
        (rsAgree F K x0 h y : ℝ) ≤ thetaRS q k * (q : ℝ) ^ u)) ∧
    (∀ h h' : Fin e → K[X], IsSpanning K q k u h → IsSpanning K q k u h' →
      (¬ ∃ c ∈ Fq F K, h' = c • h) →
      rsLine F K q k u x0 h ∩ rsLine F K q k u x0 h' = {x0}) := by sorry

end MarginMaxima.Critical
