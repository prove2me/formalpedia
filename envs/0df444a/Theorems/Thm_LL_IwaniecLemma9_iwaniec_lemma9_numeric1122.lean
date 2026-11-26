-- Prove2me | Theorems.Thm_LL_IwaniecLemma9_iwaniec_lemma9_numeric1122
-- name    : LL_IwaniecLemma9.iwaniec_lemma9_numeric1122
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-11-25T13:03:06.706585+00:00
-- url     : https://prove2.me/theorems/f68af4f8-c022-5eb0-b736-bde332964ee1
-- title:
--   Iwaniec's explicit inequality $\eta^{-1}\prod_{p\mid q}(1+p^{\eta-1})(d^{100\eta}+e^{60l^{1/4}})\le(d^{\eta}e^{l^{1/4}})^{100}$
-- statement:
--   Let $q\ge3$ be an integer, $\gamma$ real, $d=\prod_{p\mid q}p$ the product of the distinct prime divisors of $q$, $l=\log(q(|\gamma|+3))$, $\eta=\bigl(\sqrt l\,(\log 2l)^{3/4}\bigr)^{-1}$ and $M=\bigl(d^{\eta}e^{l^{1/4}}\bigr)^{100}$, all powers being real powers. Then $$\eta^{-1}\prod_{p\mid q}\bigl(1+p^{\eta-1}\bigr)\Bigl(d^{100\eta}+e^{60\,l^{1/4}}\Bigr)\le M.$$
-- source:
--   Iwaniec, Invent. Math. 23, 1974, page 102, closing inequality of the proof of Lemma 9, as used by Languasco, Pintz and Zaccagnini 2007.

import Mathlib

open Finset Real

namespace LL_IwaniecLemma9
theorem iwaniec_lemma9_numeric1122 (q : ℕ) (hq : 3 ≤ q) (γ l η M : ℝ)
    (hl : l = Real.log ((q : ℝ) * (|γ| + 3)))
    (hη : η = (Real.sqrt l * Real.log (2 * l) ^ (3 / 4 : ℝ))⁻¹)
    (hM : M = (((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ η * Real.exp (l ^ (1 / 4 : ℝ))) ^ 100) :
    η⁻¹ * (∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (η - 1))) *
      (((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ (100 * η) + Real.exp (60 * l ^ (1 / 4 : ℝ))) ≤
      M := by sorry
end LL_IwaniecLemma9
