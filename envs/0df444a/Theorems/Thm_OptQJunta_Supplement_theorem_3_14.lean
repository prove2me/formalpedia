-- Prove2me | Theorems.Thm_OptQJunta_Supplement_theorem_3_14
-- name    : OptQJunta.Supplement.theorem_3_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:15:57.703109+00:00
-- url     : https://prove2.me/theorems/bff5ee00-6baf-4b25-af17-5ab0aa8b2fad
-- title:
--   Theorem 3.14 — support size testing on $[2s]$ needs $\Omega(s/(\delta\log s))$ samples
-- statement:
--   Fix a sufficiently large integer $s$, $0<\delta<1/32$, and a constant $c>1/2$. Any randomized tester that, given independent samples from a distribution $p$ on $[2s]$, distinguishes the two cases of Problem 3.12,
--
--   1. (YES) $|\mathrm{supp}(p)|\le s$,
--   2. (NO) $\mathrm{mass}_s(p)=\max_{|S|\le s}p(S)\le1-\delta$,
--
--   with success probability at least $c$ requires
--
--   $$
--   \Omega\Big(\frac{s}{\delta\log s}\Big)
--   $$
--
--   samples, where the implicit constant depends only on $c$.
--
--   With the singleton case of Theorem 3.2 this gives the tight bound $\Theta(s/(\delta\log s))$; it is the classical ingredient of the forward-only and channel lower bounds.
--
--   **Formalization Note** There is a threshold $S$, independent of $c$, and for every $c>1/2$ a constant $\kappa>0$, such that for all $s\ge S$, all $0<\delta<1/32$ and every acceptance rule $F$ on $t$ samples with acceptance $\ge c$ on all YES distributions and $\le1-c$ on all NO distributions, $t\ge\kappa s/(\delta\log_2 s)$.
--
--   Differences from the source:
--   - reading: a sufficiently large integer s, and a constant c > 1/2 with the implicit constant depending only on c → ∃ S ∀ c > 1/2 ∃ κ > 0 ∀ s ≥ S: the threshold S is fixed before c, the constant κ depends only on c; reason: the stronger of the readings; the proof (p.37) takes s₀ from Lemma 3.17, which is independent of c, and amplifies success c to 2/3 by majority voting, which only changes the constant
--   - encoding: a randomized algorithm (tester) using t independent samples → an acceptance rule F : 𝒳^t → [0, 1], independent of the distribution, with acceptance probability E_{Y∼p^{⊗t}}[F(Y)] (sampleAcc); reason: §2.5.4 (p.23) shows every tester requesting at most t samples, adaptively and with private randomness, has exactly this form; a tester using fewer samples ignores the rest
--   - encoding: distinguishes the two cases with success probability at least c → acceptance ≥ c on every YES distribution and ≤ 1 − c on every NO distribution; reason: §2.5 (p.22): success on every promised input, no requirement outside the promise
-- source:
--   Bao, Gao, Yao, Optimal Quantum Junta Testing, preprint (version of November 3, 2026, sha256 a97d09a4…), Theorem 3.14, p.35 (Problem 3.12 and mass_s, p.35; §2.5.4, p.23)

import Mathlib
import Definitions.Def_OptQJunta_Supplement_sampleAcc

namespace OptQJunta.Supplement

/-- **Theorem 3.14** (Classical support size lower bound, adapted from the proof of [WY19,
Proposition 1]; Bao, Gao, Yao, *Optimal Quantum Junta Testing*, preprint, version of November 3, 2026, sha256 a97d09a4…, p.35). Fix a sufficiently large integer `s`, `0 < δ < 1/32`, and a
constant `c > 1/2`. Any randomized tester that, given independent samples from a distribution on
`[2s]`, distinguishes the two cases of Problem 3.12 with success probability at least `c` requires
`Ω(s/(δ log s))` samples, where the implicit constant depends only on `c`.

**Formalization Note** Problem 3.12 (p.35) with `M = 2s`: YES is `|supp(p)| ≤ s`, NO is
`mass_s(p) ≤ 1 − δ`. A tester with `t` samples is an acceptance rule `F` into `[0, 1]` (§2.5.4, p.23);
success probability `c` means acceptance `≥ c` on YES and `≤ 1 − c` on NO. "Sufficiently large" is a
threshold `S` fixed before `c`; the constant `κ > 0` depends only on `c`. `log` is base `2`. -/
theorem theorem_3_14 :
    ∃ S : ℕ, ∀ c : ℝ, 1 / 2 < c → ∃ κ : ℝ, 0 < κ ∧
      ∀ s : ℕ, S ≤ s → ∀ δ : ℝ, 0 < δ → δ < 1 / 32 →
        ∀ (t : ℕ) (F : (Fin t → Fin (2 * s)) → ℝ), IsTestFn F →
          (∀ p : Fin (2 * s) → ℝ, IsDist p → supportCard p ≤ s → c ≤ sampleAcc F p) →
          (∀ p : Fin (2 * s) → ℝ, IsDist p → massS p s ≤ 1 - δ → sampleAcc F p ≤ 1 - c) →
          κ * s / (δ * Real.logb 2 s) ≤ t := by sorry

end OptQJunta.Supplement
