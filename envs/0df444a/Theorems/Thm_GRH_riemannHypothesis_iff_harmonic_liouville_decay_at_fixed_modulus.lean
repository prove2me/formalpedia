-- Prove2me | Theorems.Thm_GRH_riemannHypothesis_iff_harmonic_liouville_decay_at_fixed_modulus
-- name    : GRH.riemannHypothesis_iff_harmonic_liouville_decay_at_fixed_modulus
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T01:45:06.782041+00:00
-- url     : https://prove2.me/theorems/2ce07fc6-d47a-4564-b96b-b2f36be2a806
-- title:
--   Ordinary RH is equivalent to harmonic Liouville decay at any single fixed modulus
-- statement:
--   Fix any integer $q\ge1$. The ordinary Riemann hypothesis is equivalent to $$\forall\,\tfrac12<\sigma<1,\quad\left|\sum_{\substack{1\le n\le U\\ (n,q)=1}}\frac{\lambda(n)}n\right|\le C_{q,\sigma}(U+1)^{\sigma-1}\quad(U\ge0).$$ In particular an individual positive modulus already detects the entire ordinary RH. For a single exponent $\sigma$, the reverse proof confines every nontrivial zeta zero to $1-\sigma\le\Re s\le\sigma$.
-- source:
--   Arithmetic converse and exact strength of the principal harmonic factor in the campaign’s squarefree bilinear decomposition (005c4a44). The proof uses Littlewood’s verified conditional Mertens theorem and its verified zero-strip converse, plus explicit finite prime and square-divisor transfers.

import Definitions.Def_GRH_SquarefreeBilinear
import Mathlib.NumberTheory.LSeries.RiemannZeta

set_option autoImplicit false

open Finset ArithmeticFunction
namespace GRH

theorem riemannHypothesis_iff_harmonic_liouville_decay_at_fixed_modulus (q : ℕ) [NeZero q] :
    RiemannHypothesis ↔
      ∀ σ : ℝ, 1/2 < σ → σ < 1 → ∃ C : ℝ, 0 ≤ C ∧ ∀ U : ℕ,
        |reducedLiouvilleHarmonic q U| ≤ C*((U:ℝ)+1)^(σ-1) := by sorry

end GRH
