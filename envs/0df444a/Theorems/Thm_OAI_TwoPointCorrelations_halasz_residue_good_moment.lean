-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_halasz_residue_good_moment
-- name    : OAI.TwoPointCorrelations.halasz_residue_good_moment
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:35.184927+00:00
-- url     : https://prove2.me/theorems/4059a39d-cb31-4a54-8057-ceedebd81c2b
-- title:
--   The fibre energy of residue-injective tuples in the Vinogradov system modulo p
-- statement:
--   Let $s,k,N,p$ be naturals with $p$ prime, $s,k>0$, $k<p$ and $N<p^k$. Let $\mathcal G$ = `halaszResidueGoodTuples (fun i : Fin k => i.castAdd s) p` be the set of tuples $x\in\{0..N-1\}^{k+s}$ whose first $k$ coordinates have pairwise distinct values of $x_i+1$ modulo $p$, and let $\phi(x)=\big(\sum_i(x_i+1)^j\big)_{j=1}^k$ (`halaszVinogradovFrequency k`). Then the fibre energy $\sum_{v}\#\{x\in\mathcal G:\phi(x)=v\}^2$ (`halaszFiberEnergy`) satisfies
--
--   $$\sum_v\#\{x\in\mathcal G:\phi(x)=v\}^2\le p^{2s}\,k^k\,p^{k(k-1)/2}\,N^k\,J_{s,k}(\lfloor N/p\rfloor+1),$$
--
--   with $J_{s,k}$ the Vinogradov count `halaszVinogradovCount` and $k(k-1)/2$ natural-number division.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.halasz_residue_good_moment`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open scoped Classical

theorem halasz_residue_good_moment {s k N p : ℕ} [Fact p.Prime]
    (hs : 0< s) (hk : 0< k) (hkp : k< p) (hNp : N< p^k) :
    halaszFiberEnergy
      (halaszResidueGoodTuples (N := N) (fun i : Fin k => i.castAdd s) p)
      (halaszVinogradovFrequency k) ≤
      p^(2*s)*((k^k*p^(k*(k-1)/2))*(N^k*halaszVinogradovCount s k (N/p+1))) := by
  sorry

end OAI.TwoPointCorrelations
