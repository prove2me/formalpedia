-- Prove2me | Theorems.Thm_OracleStateHSP_fracOracle_queryComplexity
-- name    : OracleStateHSP.fracOracle_queryComplexity
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:35:11.75584+00:00
-- url     : https://prove2.me/theorems/74ac4072-de9f-460a-b8f9-292da8dbdc6b
-- title:
--   Proof of Theorem 4.10: $Q(s, \{O^\varepsilon_f\}) \in \Theta(\log|G/H|/\sqrt\varepsilon)$
-- statement:
--   There are universal constants $c, C > 0$ such that for every $\varepsilon \in (0, 1]$, $r \ge 0$ and $m \ge 2$, the bounded-error query complexity (Definition 4.3, model of Definition 4.1) of recovering the period $s(f)$ from the fractional oracles $\{O^\varepsilon_f\}$, $f$ ranging over the Simon functions on $\mathbb Z_2^m$ with nonzero period, satisfies
--   $$
--   c\,\frac{m-1}{\sqrt\varepsilon} \;\le\; Q\bigl(s, \{O^\varepsilon_f\}_f\bigr) \;\le\; C\,\frac{m-1}{\sqrt\varepsilon}.
--   $$
--
--   The paper obtains it from (60) and Theorem 4.4; the lower half is transferred to StateHSP in Theorem 4.10.
--
--   Differences from the source:
--   - reading: Θ(log(|G/H|)/√ε) → two constants c, C > 0 chosen before ε, r and m, for all ε ∈ (0, 1], r ≥ 0, m ≥ 2; reason: log|G/H| = m − 1 on the range of Theorem 4.10
--   - encoding: answer set Z_2^m \ {0} → answer set Z_2^m; reason: an output 0 is never correct, so both answer sets give the same complexity
--   - encoding: a number → Q in ℕ∞ cast to ℝ≥0∞; reason: the absence of an algorithm is ∞
--   - encoding: the set of Simon functions on Z_2^m with nonzero period, and s returning the period → the finite type of pairs (f, s) with s ≠ 0, and the second projection; reason: a nonzero period is unique
--   - encoding: G = Z_2^n with n = r + m → the product (Fin r → ZMod 2) × (Fin m → ZMod 2); reason: Z_2^n ≅ Z_2^r ⊕ Z_2^m as groups; the paper writes G = K ⊕ V itself
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, proof of Theorem 4.10, p.40

import Mathlib
import Definitions.Def_OracleStateHSP_queryComplexity
import Definitions.Def_OracleStateHSP_SimonInst
import Definitions.Def_OracleStateHSP_fracOracle
open scoped ENNReal

namespace OracleStateHSP

/-- Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, proof of Theorem 4.10, p.40: "Using Theorem 4.4 once more, we show that recovering
`s(f)` from `O^ε_f` has bounded-error query complexity `Θ(log(|G/H|)/√ε)`."

Here: there are universal constants `c, C > 0` such that for every `ε ∈ (0, 1]`, `r ≥ 0` and
`m ≥ 2`, the bounded-error query complexity (Definition 4.3, model of Definition 4.1) of the
period `s(f)` from the oracles `{O^ε_f}`, `f` ranging over the Simon functions on `Z_2^m` with
nonzero period, satisfies `c (m − 1)/√ε ≤ Q(s, {O^ε_f}) ≤ C (m − 1)/√ε`.

**Formalization Note.** `Θ` is two constants chosen before `ε`, `r` and `m`; `log |G/H| = m − 1`;
`Q` is cast from `ℕ∞` to `ℝ≥0∞`. The answer set is `Z_2^m` (the paper's `Z_2^m \ {0}`: an
output `0` is never correct, so both sets give the same complexity). -/
theorem fracOracle_queryComplexity :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ r m : ℕ, 2 ≤ m →
      ENNReal.ofReal (c * ((m : ℝ) - 1) / Real.sqrt ε) ≤
          (queryComplexity (fun x : SimonInst m => fracOracle ε r x.fn)
            (fun x => x.period) : ℝ≥0∞) ∧
        (queryComplexity (fun x : SimonInst m => fracOracle ε r x.fn)
            (fun x => x.period) : ℝ≥0∞) ≤ ENNReal.ofReal (C * ((m : ℝ) - 1) / Real.sqrt ε) := by sorry

end OracleStateHSP
