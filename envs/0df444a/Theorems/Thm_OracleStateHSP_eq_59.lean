-- Prove2me | Theorems.Thm_OracleStateHSP_eq_59
-- name    : OracleStateHSP.eq_59
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:32:38.109442+00:00
-- url     : https://prove2.me/theorems/aac7ef65-1133-48f6-b53e-b9af0da6cbe1
-- title:
--   Eq. (59): $\gamma_2(1_{s(f)\ne s(g)} \mid (O^1_f - O^1_g)) \in \Theta(\log|G/H|)$
-- statement:
--   There are universal constants $c, C > 0$ such that for every $r \ge 0$ and $m \ge 2$, with $f, g$ ranging over the Simon functions on $\mathbb Z_2^m$ with nonzero period,
--   $$
--   c\,(m-1) \;\le\; \gamma_2\bigl(1_{s(f)\ne s(g)} \bigm| (O^1_f - O^1_g)_{f,g}\bigr) \;\le\; C\,(m-1).
--   $$
--   Here $m - 1 = \log_2|G/H|$, and $O^1_f$ is the fractional oracle at $\varepsilon = 1$ on the padded register.
--
--   This is the adversary value at $\varepsilon = 1$: the paper obtains it from Lemma 4.9 (and Simon's $O(m)$-query algorithm for the upper side) through Theorem 4.4.
--
--   Differences from the source:
--   - reading: Θ(log|G/H|) → two constants c, C > 0 chosen before r and m with c(m − 1) ≤ γ2 ≤ C(m − 1) for all r ≥ 0, m ≥ 2; reason: log|G/H| = m − 1 ≥ 1 on the range n ≥ m > 1 of Theorem 4.10
--   - encoding: real values → values in ℝ≥0∞; reason: the norm may be ∞ a priori
--   - encoding: the set of Simon functions on Z_2^m with nonzero period, and s returning the period → the finite type of pairs (f, s) with s ≠ 0, and the second projection; reason: a nonzero period is unique
--   - encoding: G = Z_2^n with n = r + m → the product (Fin r → ZMod 2) × (Fin m → ZMod 2); reason: Z_2^n ≅ Z_2^r ⊕ Z_2^m as groups; the paper writes G = K ⊕ V itself
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, eq. (59), p.40

import Mathlib
import Definitions.Def_OracleStateHSP_answerNe
import Definitions.Def_OracleStateHSP_relGamma2
import Definitions.Def_OracleStateHSP_SimonInst
import Definitions.Def_OracleStateHSP_fracOracle
open scoped ENNReal

namespace OracleStateHSP

/-- Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, eq. (59), p.40: by the characterization of Theorem 4.4, the relative `γ₂` norm for the
oracles `O^1_f` satisfies `γ₂(1_{s(f)≠s(g)} | (O^1_f − O^1_g)_{f,g}) ∈ Θ(log |G/H|)`, where `f, g`
range over the Simon functions on `Z_2^m` with nonzero period and `log |G/H| = m − 1`.

Here: there are universal constants `c, C > 0` such that for every `r ≥ 0` and `m ≥ 2`,
`c (m − 1) ≤ γ₂(…) ≤ C (m − 1)`.

**Formalization Note.** `Θ` is two constants chosen before `r` and `m`; `m ≥ 2` is the range
`n ≥ m > 1` of Theorem 4.10. `O^1_f` is `fracOracle 1 r f`; values in `ℝ≥0∞`. -/
theorem eq_59 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ r m : ℕ, 2 ≤ m →
      ENNReal.ofReal (c * ((m : ℝ) - 1)) ≤
          relGamma2 (answerNe fun x : SimonInst m => x.period)
            (fun x y => fracOracle 1 r x.fn - fracOracle 1 r y.fn) ∧
        relGamma2 (answerNe fun x : SimonInst m => x.period)
            (fun x y => fracOracle 1 r x.fn - fracOracle 1 r y.fn) ≤
          ENNReal.ofReal (C * ((m : ℝ) - 1)) := by sorry

end OracleStateHSP
