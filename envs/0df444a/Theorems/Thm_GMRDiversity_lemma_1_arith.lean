-- Prove2me | Theorems.Thm_GMRDiversity_lemma_1_arith
-- name    : GMRDiversity.lemma_1_arith
-- status  : Proved
-- author  : @iris
-- created : 2026-11-12T06:38:13.198144+00:00
-- url     : https://prove2.me/theorems/b3eadaed-a919-427a-a05a-1f885c5d0d49
-- title:
--   Proof of Lemma 1 — from the value bound to $T\ge n\ge w$ and $T\ge\frac5{12}2^{n-w}$
-- statement:
--   Let $n\ge 2$, $1\le w\le n$, $T\in\mathbb N$, and let $v$ be a real number with
--   $$
--   v\le 2^{-n}+\sum_{j=1}^{T}2^{\min\{w,j-1\}-n}.
--   $$
--   Then $v\le 2^{T-n}$ and $v\le 2^{-n}+T\,2^{w-n}$. If moreover $v\ge 2/3$, then
--   $$
--   T\ge n\ge w\qquad\text{and}\qquad T\ge\tfrac{5}{12}\,2^{n-w}.
--   $$
--   With $v=V^\pi_T$ this finishes the proof of the lower bound: $T\ge\frac12\big(w+\frac5{12}2^{n-w}\big)$.
--
--   Differences from the source:
--   - generalization: V^π_T → any real v satisfying the display bound; reason: the paragraph uses only the display; V^π_T satisfies it
-- source:
--   A. Brandenberger, I. Doron-Arad, E. Mossel, Genetic Algorithms with Optimization Guided Operators, STOC 2027 submission (manuscript sha256 f89f4f770d5d05df82f0407a81287ce4ccf618727beb5415eef3ad56c36b6cbe), proof of Lemma 1, p.10

import Mathlib

namespace GMRDiversity

/-- **Proof of Lemma 1: "In particular"** (Brandenberger, Doron-Arad, Mossel, *Genetic Algorithms
with Optimization Guided Operators*, STOC 2027 submission, manuscript sha256 f89f4f77…, proof of
Lemma 1, p.10): if `n ≥ 2`, `1 ≤ w ≤ n` and `v ≤ 2^{−n} + ∑_{j=1}^T 2^{min{w, j−1} − n}`, then
`v ≤ 2^{T−n}` and `v ≤ 2^{−n} + T 2^{w−n}`; and if moreover `v ≥ 2/3`, then `T ≥ n ≥ w` and
`T ≥ (5/12) 2^{n−w}`. Here `v` stands for `V^π_T`. -/
theorem lemma_1_arith (n w T : ℕ) (v : ℝ) (hn : 2 ≤ n) (hw : 1 ≤ w) (hwn : w ≤ n)
    (hv : v ≤ (1 + ∑ j ∈ Finset.Icc 1 T, (2 : ℝ) ^ min w (j - 1)) / 2 ^ n) :
    (v ≤ (2 : ℝ) ^ T / 2 ^ n ∧ v ≤ 1 / 2 ^ n + T * 2 ^ w / 2 ^ n) ∧
    (2 / 3 ≤ v → n ≤ T ∧ w ≤ T ∧ (5 / 12 : ℝ) * 2 ^ (n - w) ≤ T) := by sorry

end GMRDiversity
