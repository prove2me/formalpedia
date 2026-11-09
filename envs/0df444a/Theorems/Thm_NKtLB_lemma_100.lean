-- Prove2me | Theorems.Thm_NKtLB_lemma_100
-- name    : NKtLB.lemma_100
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:13:21.72648+00:00
-- url     : https://prove2.me/theorems/39a410c9-d83e-4eec-9a35-e285c7b2f454
-- title:
--   Lemma 100 — randomness-efficient success amplification for rK
-- statement:
--   There is a constant $c$ such that the following holds. Let $O$ be an oracle, let $t,n,m,r,l\in\mathbb N$, let $\delta\in(0,1]$, and let $x\in\{0,1\}^n$, $y\in\{0,1\}^m$ with $0<n<t$. Then
--   $$
--   \mathrm{rK}^{(\mathrm{poly}(t/\delta);\,2r),O^{\le l}}_{2/3}(x\mid y)\ \le\ \mathrm{rK}^{(t;r),O^{\le l}}_\delta(x\mid y)+O\bigl(\log(n/\delta)\bigr),
--   $$
--   with $\mathrm{poly}(t/\delta)=\lceil c(t/\delta)^c\rceil+c$ and $O(\log(n/\delta))=c\log(n/\delta)+c$.
--
--   So a description that succeeds with probability $\delta$ can be amplified to success probability $2/3$ at a cost of $O(\log(n/\delta))$ bits while only doubling the number of random bits. Corollary 104 relies on this saving of randomness.
--
--   Here $\mathrm{nKt}$, $\mathrm{nK}$ and $\mathrm{rK}$ are taken with respect to any valid universal machine $U$ (time-efficient, simulating every machine with quasi-linear overhead).
--
--   Differences from the source:
--   - generalization: a fixed time-efficient universal machine $U$ (p.22) → every pair (U, code) with `IsValidUniversal U code`; reason: the paper uses only time-efficiency and $\tilde O$-overhead simulation of $U$; its fixed $U$ is one such pair
--   - encoding: $O(f)$, $\mathrm{poly}(f)$ → $C f+C$, $\lceil C f^C\rceil+C$ with $C$ quantified before the data; reason: standard meaning; constants are chosen in the order the statement reads
--   - encoding: $n\ge0$ with $O(\log n/\delta)$ → $0<n$; reason: $\log(n/\delta)$ is undefined at $n=0$
--   - encoding: complexities with $\min\emptyset=\infty$ → values in $\mathbb N\cup\{\infty\}$ compared in `EReal`; reason: $\infty\pm a=\infty$ for real $a$ matches the paper
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Lemma 100, p.67

import Mathlib
import Definitions.Def_NKtLB_IsValidUniversal
import Definitions.Def_NKtLB_rK
import Definitions.Def_NKtLB_toEReal

namespace NKtLB

/-- **Lemma 100 (randomness-efficient success amplification for `rK`)** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Lemma 100, p.67):
"For any oracle `O`, any time bound `t ∈ ℕ`, any length `n, m, r, l ∈ ℕ`, any real number
`δ ∈ (0, 1]`, and any strings `x ∈ {0,1}^n`, `y ∈ {0,1}^m` satisfying `n < t`, we have
`rK^{(poly(t/δ);2r),O^{≤l}}_{2/3}(x | y) ≤ rK^{(t;r),O^{≤l}}_δ(x | y) + O(log n/δ)`."

**Formalization Note.** `poly(t/δ)` is `⌈c·(t/δ)^c⌉ + c` and `O(log n/δ)` is `c·log₂(n/δ) + c`, one
`c` (depending only on `U`) before all data. `0 < n` excludes `n = 0`, where `log(n/δ)` is
undefined. Comparison in `EReal` with `rK = ∞` allowed on either side. -/
theorem lemma_100 (U : Machine) (code : Machine → List Bool) (hU : IsValidUniversal U code) :
    ∃ c : ℕ, ∀ (O : Set (List Bool)) (t n m r l : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ x y : List Bool, x.length = n → y.length = m → n < t → 0 < n →
        toEReal (rK U O l (⌈(c : ℝ) * ((t : ℝ) / δ) ^ c⌉₊ + c) (2 * r) (2 / 3) x y) ≤
          toEReal (rK U O l t r δ x y) + ((c * Real.logb 2 ((n : ℝ) / δ) + c : ℝ) : EReal) := by sorry

end NKtLB
