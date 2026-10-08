-- Prove2me | Theorems.Thm_LLLFactor_Factors_mignotte_step
-- name    : LLLFactor.Factors.mignotte_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:22:28.871147+00:00
-- url     : https://prove2.me/theorems/dbcd2080-ea65-4568-8195-843299dd7632
-- title:
--   Proof of (2.13), p. 528 — Mignotte's bound |g| ≤ C(2m, m)^{1/2}·|f| for a divisor g of f of degree ≤ m
-- statement:
--   Let $f\in\mathbb Z[X]$ be nonzero, let $m\ge0$ be an integer, and let $g\in\mathbb Z[X]$ divide $f$ in $\mathbb Z[X]$ with $\deg g\le m$. Then
--   $$|g|\le\binom{2m}{m}^{1/2}\cdot|f|,$$
--   where $|\cdot|$ is the Euclidean length of the coefficient vector.
--
--   This is the "result of Mignotte" that the proofs of (2.13) and (2.16) apply to $g=h_0$: factors of $f$ of bounded degree have bounded coefficients, so $h_0$ is a short vector of the lattice $L$.
--
--   **Formalization Note** The page applies the bound to $h_0$ under the hypothesis $\deg h_0\le m$; here it is stated for every divisor $g$ of $f$ of degree at most $m$, which is the form of the cited result (Mignotte 1974; Knuth, Exercise 4.6.2.20) and the form re-used in the proof of (2.16). The hypothesis $f\ne0$ comes from $\deg f=n>0$ in the setting; without it every $g$ would divide $f=0$.
-- source:
--   Lenstra, Lenstra, Lovász, Factoring polynomials with rational coefficients, Math. Ann. 261 (1982), p. 528, proof of (2.13) Proposition (citing Mignotte [10] and Knuth [7, Exercise 4.6.2.20])

import Mathlib
import Definitions.Def_LLLFactor_Factors_Setting

open Polynomial

namespace LLLFactor.Factors

theorem mignotte_step (f : ℤ[X]) (hf : f ≠ 0) (m : ℕ) (g : ℤ[X]) (hgf : g ∣ f)
    (hgm : g.natDegree ≤ m) :
    polyNorm g ≤ ((Nat.choose (2 * m) m : ℕ) : ℝ) ^ ((1 : ℝ) / 2) * polyNorm f := by sorry

end LLLFactor.Factors
