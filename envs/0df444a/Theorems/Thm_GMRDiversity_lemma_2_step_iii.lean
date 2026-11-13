-- Prove2me | Theorems.Thm_GMRDiversity_lemma_2_step_iii
-- name    : GMRDiversity.lemma_2_step_iii
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:39:49.156115+00:00
-- url     : https://prove2.me/theorems/5bd740f7-53d1-4014-ac14-867aab103d2f
-- title:
--   Proof of Lemma 2, Step (iii) — successful seeds and $\mathbb P(\widehat x=x)\ge\frac{2^s-1}{2^n-1}\ge2^{-d-1}$
-- statement:
--   Let $S\le\mathbb F_2^n$ be nondegenerate of dimension $s$, let $q\in S$ and $h_*:=x+q\in H=S^\perp$. Then:
--
--   1. the guess $\widehat x:=q+h_A$ equals $x$ exactly when $h_A=h_*$;
--   2. the successful nonzero seeds, the nonzero $A\in S+h_*$, number
--   $$
--   \#\{A\ne0 : A\in S+h_*\}=\begin{cases}2^s-1,&h_*=0,\\ 2^s,&h_*\ne0;\end{cases}
--   $$
--   3. for $1\le s\le n$, with $d:=n-s$,
--   $$
--   \frac{2^s-1}{2^n-1}\ge 2^{-d-1}=:\eta;
--   $$
--   4. if $w-4\le s\le n$ and $w\le n$, then $d\le n-w+4$ and $\eta^{-1}=2^{d+1}\le 2^{n-w+5}$;
--   5. for $n\ge2$, the expected number $2^n/(2^n-1)$ of generations until a nonzero seed is less than $2$.
--
--   Since a seed $A$ conditioned on $A\ne0$ is uniform on the $2^n-1$ nonzero vectors, items 2 and 3 give $\mathbb P(\widehat x=x)\ge(2^s-1)/(2^n-1)\ge\eta$.
--
--   Differences from the source:
--   - encoding: P(x̂ = x) ≥ (2^s − 1)/(2^n − 1) ≥ 2^{−d−1} → the exact count of successful nonzero seeds and the inequality (2^s − 1)/(2^n − 1) ≥ 1/2^{n−s+1}; reason: a nonzero seed is uniform on 2^n − 1 vectors, so the probability is the count over 2^n − 1
--   - encoding: s from Step (i) (w − 4 ≤ s ≤ w − 3) and n ≥ 2 from Lemma 2 → the hypotheses w ≤ s + 4, s ≤ n, w ≤ n and 2 ≤ n on the clauses that use them; reason: the context of Step (iii), stated where it is used
-- source:
--   A. Brandenberger, I. Doron-Arad, E. Mossel, Genetic Algorithms with Optimization Guided Operators, STOC 2027 submission (manuscript sha256 f89f4f770d5d05df82f0407a81287ce4ccf618727beb5415eef3ad56c36b6cbe), proof of Lemma 2, Step (iii), p.11

import Mathlib
import Definitions.Def_GMRDiversity_Nondeg

namespace GMRDiversity

open ExtremalForrelation.Nonadaptive

/-- **Proof of Lemma 2, Step (iii)** (Brandenberger, Doron-Arad, Mossel, *Genetic Algorithms with
Optimization Guided Operators*, STOC 2027 submission, manuscript sha256 f89f4f77…, proof of Lemma 2,
Step (iii), p.11): let `S ≤ 𝔽₂ⁿ` be nondegenerate of dimension `s`, `q ∈ S`, and
`h_* := x + q ∈ H = S^⊥`. Then
1. the guess `x̂ := q + h_A` equals `x` exactly when `h_A = h_*`;
2. the successful nonzero seeds, the nonzero `A ∈ S + h_*`, number `2^s − 1` if `h_* = 0` and `2^s`
   otherwise;
3. for `1 ≤ s ≤ n`, `(2^s − 1)/(2ⁿ − 1) ≥ 2^{−d−1} =: η` with `d := n − s`;
4. if `w − 4 ≤ s ≤ n` and `w ≤ n`, then `d ≤ n − w + 4` and `η^{−1} = 2^{d+1} ≤ 2^{n−w+5}`;
5. for `n ≥ 2`, the expected number `2ⁿ/(2ⁿ − 1)` of generations until a nonzero seed is below `2`. -/
theorem lemma_2_step_iii {n s w : ℕ} (S : Submodule (ZMod 2) (V n)) (hS : Nondeg S)
    (hs : Module.finrank (ZMod 2) S = s) (x q hstar : V n) (hq : q ∈ S)
    (hstar_def : hstar = x + q) (hstar_mem : hstar ∈ orth S) :
    (∀ hA : V n, q + hA = x ↔ hA = hstar) ∧
    Nat.card {A : V n // A ≠ 0 ∧ A - hstar ∈ S} = (if hstar = 0 then 2 ^ s - 1 else 2 ^ s) ∧
    (1 ≤ s → s ≤ n → 1 / (2 : ℝ) ^ (n - s + 1) ≤ ((2 : ℝ) ^ s - 1) / (2 ^ n - 1)) ∧
    (w ≤ s + 4 → s ≤ n → w ≤ n → n - s ≤ n - w + 4 ∧ 2 ^ (n - s + 1) ≤ 2 ^ (n - w + 5)) ∧
    (2 ≤ n → (2 : ℝ) ^ n / (2 ^ n - 1) < 2) := by sorry

end GMRDiversity
