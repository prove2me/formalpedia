-- Prove2me | Theorems.Thm_KnapsackFPRAS_corollary_3_4
-- name    : KnapsackFPRAS.corollary_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:36:58.74792+00:00
-- url     : https://prove2.me/theorems/401d80f5-3e56-4709-8e05-a22b279dc12a
-- title:
--   Corollary 3.4 — $\mathbb E_{X\sim Q_w}|X\cap I_m|\le2m$
-- statement:
--   Assume $1\le w_i\le T$ for all $i$ and $\sum_i w_i>T$ (the standing assumption (7)). Let $\lambda$ be a tilt with $\mathbb E_{X\sim Q^\lambda_w}[w(X)]\le2T$, which the tilt of Lemma 3.2 satisfies. For $m\ge1$ let $I_m:=\{i: T/m<w_i\le2T/m\}$. Then
--
--   $$
--   \mathbb E_{X\sim Q^\lambda_w}\bigl[|X\cap I_m|\bigr]\le2m .
--   $$
--
--   This bounds how many items of each weight class a tilted subset contains on average, which keeps the counting tables of Section 4 small.
--
--   Differences from the source:
--   - reading: the corollary as printed in §3.3 → hypotheses 1 ≤ wᵢ ≤ T and T < ∑ wᵢ; reason: standing assumption (7) of §2 (p.9)
--   - generalization: Q_w with the tilt λ of Lemma 3.2 → Q^λ_w for every real λ with E_{X∼Q^λ_w}[w(X)] ≤ 2T; reason: the proof uses only this guarantee of Lemma 3.2; its λ is one such
--   - generalization: m ≥ 1 (the paper uses powers of two) → every real m ≥ 1; reason: covers every integer m ≥ 1
--   - encoding: E_{X∼Q_w}[|X ∩ I_m|] → the finite sum ∑_X Q(X)|X ∩ I_m|; reason: same quantity
-- source:
--   Jin–Park–Saha, A Nearly Linear-Time FPRAS for Counting Knapsack, STOC 2027 submission (manuscript sha256 c117260b…), Corollary 3.4, p.14 (PDF p.15)

import Mathlib
import Definitions.Def_KnapsackFPRAS_Tilt
import Definitions.Def_KnapsackFPRAS_Rounding

set_option autoImplicit false

namespace KnapsackFPRAS

/-- **Corollary 3.4**, p.14. "For 𝑚 ≥ 1, let 𝐼_𝑚 := {𝑖 : 𝑇/𝑚 < 𝑤𝑖 ≤ 2𝑇/𝑚}. Then
E_{𝑋∼𝑄_𝑤}[|𝑋 ∩ 𝐼_𝑚|] ≤ 2𝑚."

Jin–Park–Saha, *A Nearly Linear-Time FPRAS for Counting Knapsack*, STOC 2027 submission
(manuscript sha256 c117260b…4af0), Corollary 3.4, p.14 (PDF p.15).

**Formalization Note.** Under the standing assumption (7). `Q_w` is the tilt of Lemma 3.2 (§3.3);
the statement holds for every real `λ` with `E_{X∼Q^λ_w}[w(X)] ≤ 2T`, the guarantee of
Lemma 3.2 that the proof uses, and for every real `m ≥ 1`. The expectation is the finite sum
`∑_X Q^λ_w(X)|X ∩ I_m|`. -/
theorem corollary_3_4 {n : ℕ} (w : Fin n → ℕ) (T : ℕ)
    (hw : ∀ i, 1 ≤ w i ∧ w i ≤ T) (hsum : T < ∑ i, w i)
    (lam : ℝ) (hexp : Tilt.expWeight (fun i => (w i : ℝ)) lam ≤ 2 * T)
    (m : ℝ) (hm : 1 ≤ m) :
    ∑ X : Finset (Fin n), Tilt.Q (fun i => (w i : ℝ)) lam X *
      ((X ∩ Rounding.classIdx T w m).card : ℝ) ≤ 2 * m := by sorry

end KnapsackFPRAS
