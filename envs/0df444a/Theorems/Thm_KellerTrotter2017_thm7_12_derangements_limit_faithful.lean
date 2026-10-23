-- Prove2me | Theorems.Thm_KellerTrotter2017_thm7_12_derangements_limit_faithful
-- name    : KellerTrotter2017.thm7_12_derangements_limit_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T01:26:51.867632+00:00
-- url     : https://prove2.me/theorems/770770fe-9fbc-4660-ba7a-6a235d1120cd
-- title:
--   Theorem 7.12 — the proportion of derangements tends to $1/e$
-- statement:
--   For a positive integer $n$ let $d_n$ be the number of derangements of $[n]$, i.e. permutations $\sigma$ of $[n]$ with $\sigma(x) \ne x$ for every $x$. Then
--
--   $$\lim_{n \to \infty} \frac{d_n}{n!} = \frac{1}{e}.$$
--
--   This is Theorem 7.12 of Keller and Trotter, *Applied Combinatorics*, the asymptotic consequence of the derangement formula (Theorem 7.11, a milestone of this mission).
--
--   **Formalization Note** The sequence is indexed from $n = 0$; a single term does not affect the limit.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 148, Theorem 7.12

import Mathlib

theorem KellerTrotter2017.thm7_12_derangements_limit_faithful :
    Filter.Tendsto
      (fun n : ℕ => (Fintype.card {σ : Equiv.Perm (Fin n) // ∀ x, σ x ≠ x} : ℝ) / (n.factorial : ℝ))
      Filter.atTop (nhds (Real.exp (-1))) := by sorry
