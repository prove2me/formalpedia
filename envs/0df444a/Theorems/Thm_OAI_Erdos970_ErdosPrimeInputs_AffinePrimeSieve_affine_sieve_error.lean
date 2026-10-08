-- Prove2me | Theorems.Thm_OAI_Erdos970_ErdosPrimeInputs_AffinePrimeSieve_affine_sieve_error
-- name    : OAI.Erdos970.ErdosPrimeInputs.AffinePrimeSieve.affine_sieve_error
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:22.71495+00:00
-- url     : https://prove2.me/theorems/2110eec9-b31d-4e7b-a82d-b934b2f055a6
-- title:
--   Fundamental-lemma sieve bound for an affine progression, with error J·W(P)·e^{−s/96} + 2u^s
-- statement:
--   Let $N\in\mathbb N$, $a\in\mathbb Z$, $q\in\mathbb N$, and let $P$ be a finite set of primes, each at most $u$ and each coprime to $q$. Let $u\ge2$, $s\ge480024$, and $J\ge0$ with $|N-J|\le1$. Write `survivors N a q P` for the set of $i\in\{0,1,\dots,N-1\}$ such that $a+qi$ is divisible by no prime of $P$, and $W(P)=\prod_{p\in P}(1-1/p)$ (`euler P`). Then
--
--   $$\Big|\#\,\mathrm{survivors}(N,a,q,P)-J\,W(P)\Big|\le J\,W(P)\,e^{-s/96}+2u^{s}.$$
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.Erdos970.ErdosPrimeInputs.AffinePrimeSieve.affine_sieve_error`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.Erdos970.ErdosPrimeInputs.AffinePrimeSieve

open scoped _root_.Erdos970
open Finset
open OAI.Erdos970.NumberTheoryLean
open IntervalBoundingSieve
open OAI.Erdos970.ErdosPrimeInputs.SubsetPrimeSieve
open OAI.Erdos970.ErdosPrimeInputs.PrimeProductOmissions

theorem affine_sieve_error (N : ℕ) (a : ℤ) (q : ℕ) (u s J : ℝ) (P : Finset ℕ)
    (hu : 2 ≤ u) (hs : 480024 ≤ s) (hJ : 0 ≤ J) (hNJ : |(N:ℝ)-J| ≤ 1)
    (hP : ∀ p ∈ P, p.Prime) (hsize : ∀ p ∈ P, (p:ℝ) ≤ u)
    (hcop : ∀ p ∈ P, q.Coprime p) :
    |((survivors N a q P).card : ℝ) - J*euler P| ≤
      J*euler P*Real.exp (-s/96) + 2*u^s := by
  sorry

end OAI.Erdos970.ErdosPrimeInputs.AffinePrimeSieve
