-- Prove2me | Theorems.Thm_LowErrExt_Supplement_theorem_1_3
-- name    : LowErrExt.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:34:11.550143+00:00
-- url     : https://prove2.me/theorems/2c01fc72-1d78-452b-826e-72ef8d1c5717
-- title:
--   Theorem 1.3 — approximate duality: biased $\mathsf{IP}$ is constant on subsets of density $2^{-\ell}$, $\ell=C(n^C\log(1/\varepsilon))^{1/(C+1)}$
-- statement:
--   There is a universal constant $C\ge1$ such that the following holds. Let $X,Y\subseteq\mathbb F_2^n$ and $\varepsilon>0$. If
--   $$\mathrm{bias}[\mathsf{IP}(X,Y)]\ge\varepsilon,$$
--   then there are subsets $X'\subseteq X$, $Y'\subseteq Y$ with $|X'|\ge 2^{-\ell}|X|$, $|Y'|\ge2^{-\ell}|Y|$ and $\mathrm{bias}[\mathsf{IP}(X',Y')]=1$, where
--   $$\ell=C\big(n^C\log(1/\varepsilon)\big)^{1/(C+1)}.$$
--
--   This is a polynomial form of the approximate duality conjecture of Ben-Sasson and Ron-Zewi: a biased inner product is constant on a large rectangle.
--
--   **Formalization Note** $\mathrm{bias}[\mathsf{IP}(X,Y)]$ is `setBias`; logarithms are base 2; $C$ is chosen before $n$, the sets and $\varepsilon$.
--
--   Differences from the source:
--   - encoding: ε unrestricted (log(1/ε) in ℓ) → 0 < ε; reason: log(1/ε) is undefined for ε ≤ 0; for ε > 1 the hypothesis cannot hold, so no instance changes
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Theorem 1.3, p.7

import Mathlib
import Definitions.Def_LowErrExt_Supplement_setBias

namespace LowErrExt.Supplement

/-- **Theorem 1.3 (Approximate duality).**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Theorem 1.3, p.7: "Let X, Y ⊆ F₂ⁿ. If bias[IP(X, Y)] ≥ ε, then there exist subsets X′ ⊆ X, Y′ ⊆ Y
of size |X′| ≥ 2^{−ℓ}|X| and |Y′| ≥ 2^{−ℓ}|Y| such that bias[IP(X′, Y′)] = 1, where
ℓ := C(n^C log(1/ε))^{1/(C+1)} for some universal constant C ≥ 1."

**Formalization Note.** `C ≥ 1` is universal: it is chosen before `n`, the sets and `ε`. The bias of
two sets is `setBias` (§1.2, p.6). `ε > 0` is required (for `ε ≤ 0`, `log(1/ε)` is undefined); for
`ε > 1` the hypothesis cannot hold, and at `ε = 1` the loss is `ℓ = 0`. Logarithms are base 2.
The size bounds are cardinality bounds. -/
theorem theorem_1_3 :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (n : ℕ) (X Y : Finset (Fin n → ZMod 2)) (ε : ℝ), 0 < ε → ε ≤ setBias X Y →
        ∃ X' Y' : Finset (Fin n → ZMod 2), X' ⊆ X ∧ Y' ⊆ Y ∧
          (2 : ℝ) ^ (-(C * ((n : ℝ) ^ C * Real.logb 2 (1 / ε)) ^ (1 / (C + 1)))) * (X.card : ℝ) ≤
            (X'.card : ℝ) ∧
          (2 : ℝ) ^ (-(C * ((n : ℝ) ^ C * Real.logb 2 (1 / ε)) ^ (1 / (C + 1)))) * (Y.card : ℝ) ≤
            (Y'.card : ℝ) ∧
          setBias X' Y' = 1 := by sorry

end LowErrExt.Supplement
