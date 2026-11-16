-- Prove2me | Theorems.Thm_HWMaskLeak_Supplement_theorem_1
-- name    : HWMaskLeak.Supplement.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:01:01.17706+00:00
-- url     : https://prove2.me/theorems/8cd8fbc5-00da-4d4b-a9da-b54ecbfc249b
-- title:
--   Theorem 1 — prime-exponent Mersenne moduli: $E_k(s)\le C\,n^{-k/2+1}\log n$ with $C$ absolute
-- statement:
--   Let $G=\mathbb Z/N\mathbb Z$ and let $E_k(s)$ be the insecurity of a uniform $k$-party additive sharing of $s\in G$ under Hamming-weight leakage, eq. (1): the total variation distance between the law of the $k$ leaked weights for the secret $s$ and for a uniform secret.
--
--   There is an absolute constant $C>0$ such that the following holds. Let $n\ge3$ be prime and $N=2^n-1$ (the modulus $N$ itself need not be prime). For every integer $k\ge3$ and every $s\in\mathbb Z/N\mathbb Z$,
--   $$
--   E_k(s)\le C\,n^{-k/2+1}\log n,
--   $$
--   and consequently $E_k:=\max_{s\in G}E_k(s)\le C\,n^{-k/2+1}\log n$.
--
--   For prime exponents this improves the bound $n^{-k/2+5/4}$ of the near-dyadic theorem by a factor $n^{-1/4}\log n$, with a constant independent of $k$.
--
--   **Formalization Note** $\log$ is the natural logarithm and multiplies the real power $n^{-k/2+1}$. The constant $C$ is chosen before $n$, $N$, $k$ and $s$.
--
--   Differences from the source:
--   - encoding: E_k(s) ≪ n^{−k/2+1} log n (≪ without subscript) → ∃ C > 0 chosen before n, N, k, s with E_k(s) ≤ C · n^{−k/2+1} · Real.log n; reason: p.16: an unsubscripted ≪ has an absolute constant; footnote 1, p.7 confirms Theorem 1's constant is absolute
--   - encoding: Consequently, E_k = max_s E_k(s) ≪ n^{−k/2+1} log n → Finset.univ.sup' over ZMod N of insecurity N k ≤ the same bound, with the same C; reason: E_k := max_{s∈G} E_k(s) (p.16); the max over a finite nonempty set is Finset.sup'
--   - encoding: N = 2ⁿ − 1 and s ∈ ℤ/Nℤ → N : ℕ with [NeZero N] and hN : N = 2 ^ n - 1, s : ZMod N; reason: N = 2ⁿ − 1 ≥ 7 for n ≥ 3, so NeZero excludes nothing; ZMod N is ℤ/Nℤ with canonical representatives ZMod.val
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360358eddae84b7b4ee1bbb418105b7887539046e553046bbedd46125a9), Theorem 1, p.18 (pdf p.18); constant convention p.16 and footnote 1, p.7

import Mathlib
import Definitions.Def_HWMaskLeak_insecurity

namespace HWMaskLeak.Supplement

open HWMaskLeak

/-- **Theorem 1 (prime-exponent Mersenne-moduli upper bound)** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak Their Weight: From Additive Sharing to
Learning with Physical Rounding*, preprint (version of October 31, 2026, sha256 ab686360…), Theorem 1, p.18):
let `n ⩾ 3` be prime and `N = 2ⁿ − 1` (`N` itself need not be prime). For every fixed `k ⩾ 3` and
every `s ∈ ℤ/Nℤ`, `E_k(s) ≪ n^{−k/2+1} log n`; consequently `E_k = max_s E_k(s) ≪ n^{−k/2+1} log n`.

**Formalization Note** `E_k(s)` is the published `insecurity N k s` (eq. (1)). The `≪` carries no
subscript, so by the convention of p.16 (and footnote 1, p.7: "an absolute implied constant") the
constant `C` is absolute: it is chosen before `n, N, k, s`. `log` is the natural logarithm, outside
the real power `n^{−k/2+1}`. `N = 2ⁿ − 1 ⩾ 7`, so `[NeZero N]` excludes nothing. -/
theorem theorem_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n N k : ℕ) [NeZero N], n.Prime → 3 ≤ n → N = 2 ^ n - 1 → 3 ≤ k →
      (∀ s : ZMod N,
        insecurity N k s ≤ C * (n : ℝ) ^ (-(k : ℝ) / 2 + 1) * Real.log n) ∧
      Finset.univ.sup' Finset.univ_nonempty (insecurity N k) ≤
        C * (n : ℝ) ^ (-(k : ℝ) / 2 + 1) * Real.log n := by sorry

end HWMaskLeak.Supplement
