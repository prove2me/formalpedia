-- Prove2me | Theorems.Thm_NKtLB_exists_nKt_incompressible
-- name    : NKtLB.exists_nKt_incompressible
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:10:49.854066+00:00
-- url     : https://prove2.me/theorems/5897ad58-1600-4490-a35f-7be8e7608914
-- title:
--   Proof of Claim 108 — a string $x\in\{0,1\}^n$ with $\mathrm{nKt}(x\mid y)\ge n$
-- statement:
--   For every string $y$ and every $n\in\mathbb N$ there is $x\in\{0,1\}^n$ with
--   $$
--   \mathrm{nKt}(x\mid y)\ \ge\ n .
--   $$
--
--   This is the counting argument (Lemma 23 for nKt) used in the proof of Claim 108 with $y=s_{i-1}$. It supplies the first argument $x$ of the generator $G_1$ in each round of Algorithm 1.
--
--   Differences from the source:
--   - generalization: $y=s_{i-1}$, $\mathrm{nKt}$ for the fixed universal $U$ → every string $y$ and every machine $U$; reason: the counting argument uses only that a program nondeterministically outputs at most one string, which holds for every machine of this model because the guess tape is read sequentially
--   - encoding: complexities with $\min\emptyset=\infty$ → values in $\mathbb N\cup\{\infty\}$ compared in `EReal`; reason: $\infty\pm a=\infty$ for real $a$ matches the paper
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), proof of Claim 108, p.76 (Lemma 23, p.24)

import Mathlib
import Definitions.Def_NKtLB_nKt

namespace NKtLB

/-- **A string incompressible given `y`** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), proof of Claim 108, p.76, using Lemma 23 for
`nKt`): "By a counting argument (Lemma 23), there also exists some `x ∈ {0,1}^n` such that
`nKt(x | s_{i−1}) ≥ n`."

For every machine `U`, every string `y` and every `n` there is `x ∈ {0,1}^n` with `nKt(x | y) ≥ n`.

**Formalization Note.** Stated for every conditional string `y` (the paper's instance is
`y = s_{i−1}`) and for every machine `U`, not only valid universal ones: the counting argument
uses only that a program nondeterministically outputs at most one string, which holds in this model
because the guess tape is read sequentially. -/
theorem exists_nKt_incompressible (U : Machine) (y : List Bool) (n : ℕ) :
    ∃ x : List Bool, x.length = n ∧ (n : ℕ∞) ≤ nKt U ∅ ⊤ x y [] := by sorry

end NKtLB
