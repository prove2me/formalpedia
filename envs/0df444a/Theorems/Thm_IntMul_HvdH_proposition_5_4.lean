-- Prove2me | Theorems.Thm_IntMul_HvdH_proposition_5_4
-- name    : IntMul.HvdH.proposition_5_4
-- status  : Open
-- author  : @avi
-- created : 2026-10-09T00:41:04.230979+00:00
-- url     : https://prove2.me/theorems/8cac1eed-529c-4a97-9a71-6c6617876ad3
-- title:
--   HvdH Proposition 5.4: $M(n) < \frac{12T}{r}M(3rp) + O(n\log n)$
-- statement:
--   Fix an integer $d \ge 2$. There is a deterministic multitape Turing machine $M$ (in the model of `Definitions.Def_IntMul_MultitapeModel`) that correctly multiplies $n$-bit integers for every $n \ge 1$, and a constant $C$ (depending on $d$ and $M$) such that the following holds. For every $n \ge n_0 := 2^{d^{12}}$, let
--   $$b = \lceil \log_2 n\rceil,\qquad p = 6b,$$
--   let $T$ be the unique power of two with $4n/b \le T < 8n/b$, and let $r$ be the unique power of two with $T^{1/d} \le r < 2T^{1/d}$. Writing $\mathcal M(m) := \inf\{\tau : \mathrm{MultipliesAt}(M, m, \tau)\}$ for the worst-case running time of $M$ on $m$-bit inputs,
--   $$\mathcal M(n) \;<\; \frac{12\,T}{r}\,\mathcal M(3rp) \;+\; C\, n\log n .$$
--
--   This is the recursive step of the Harvey–van der Hoeven algorithm (eq. (5.14)): an $n$-bit product is reduced, via Agarwal–Cooley, Gaussian resampling (Theorem 4.1) and Bluestein/Rader/Kronecker substitution (Propositions 5.2, 5.3), to $12T/r$ multiplications of size $3rp$, plus $O(n\log n)$ overhead. The same machine $M$ appears on both sides (it calls itself recursively).
--
--   Formalization notes: $\log$ is the natural logarithm; $T^{1/d}$ is a real power; $\lceil\log_2 n\rceil$ is `Nat.clog 2 n`; the universally quantified $b,p,T,r$ are pinned down uniquely by the hypotheses, so the statement is never vacuous. The constant $C$ is an arbitrary real (no sign restriction).
-- source:
--   D. Harvey, J. van der Hoeven, Integer multiplication in time O(n log n), Ann. of Math. 193 (2021), https://doi.org/10.4007/annals.2021.193.2.4 (preprint https://hal.science/hal-02070778v2), Proposition 5.4, eq. (5.14), p. 40; parameters from §5 (n0 = 2^{d^12}), (5.1) b, (5.2) p, (5.6) T, (5.7) r, pp. 36-37

import Mathlib
import Definitions.Def_IntMul_MultitapeModel

namespace IntMul.HvdH

theorem proposition_5_4 (d : ℕ) (hd : 2 ≤ d) :
    ∃ M : MultitapeTM, (∀ n : ℕ, 1 ≤ n → ∃ τ : ℝ, MultipliesAt M n τ) ∧
      ∃ C : ℝ, ∀ n : ℕ, 2 ^ (d ^ 12) ≤ n →
        ∀ b p T r : ℕ, b = Nat.clog 2 n → p = 6 * b →
          (∃ k : ℕ, T = 2 ^ k) → 4 * (n : ℝ) / b ≤ T → (T : ℝ) < 8 * (n : ℝ) / b →
          (∃ j : ℕ, r = 2 ^ j) → (T : ℝ) ^ ((1 : ℝ) / d) ≤ r → (r : ℝ) < 2 * (T : ℝ) ^ ((1 : ℝ) / d) →
          sInf {τ : ℝ | MultipliesAt M n τ} <
            12 * (T : ℝ) / r * sInf {τ : ℝ | MultipliesAt M (3 * r * p) τ} +
              C * ((n : ℝ) * Real.log n) := by sorry

end IntMul.HvdH
