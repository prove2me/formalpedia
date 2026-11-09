-- Prove2me | Theorems.Thm_OracleStateHSP_eq_60
-- name    : OracleStateHSP.eq_60
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:32:42.35942+00:00
-- url     : https://prove2.me/theorems/38bd36b1-0b79-44b9-b535-ef62dca9446b
-- title:
--   Eq. (60): $\gamma_2(\cdot \mid O^\varepsilon) = \gamma_2(\cdot \mid O^1)/\sqrt\varepsilon \in \Theta(\log|G/H|/\sqrt\varepsilon)$
-- statement:
--   There are universal constants $c, C > 0$ such that for every $\varepsilon \in (0, 1]$, $r \ge 0$ and $m \ge 2$, with $f, g$ ranging over the Simon functions on $\mathbb Z_2^m$ with nonzero period,
--   $$
--   \gamma_2\bigl(1_{s(f)\ne s(g)} \bigm| (O^\varepsilon_f - O^\varepsilon_g)_{f,g}\bigr) = \frac{1}{\sqrt\varepsilon}\, \gamma_2\bigl(1_{s(f)\ne s(g)} \bigm| (O^1_f - O^1_g)_{f,g}\bigr)
--   $$
--   and
--   $$
--   c\,\frac{m-1}{\sqrt\varepsilon} \;\le\; \gamma_2\bigl(1_{s(f)\ne s(g)} \bigm| (O^\varepsilon_f - O^\varepsilon_g)_{f,g}\bigr) \;\le\; C\,\frac{m-1}{\sqrt\varepsilon}.
--   $$
--
--   The equality is Fact 4.5 with $c = \sqrt\varepsilon$ applied to the identity (58).
--
--   Differences from the source:
--   - reading: Θ(log|G/H|/√ε) → two constants c, C > 0 chosen before ε, r and m with c(m − 1)/√ε ≤ γ2 ≤ C(m − 1)/√ε for all ε ∈ (0, 1], r ≥ 0, m ≥ 2; reason: log|G/H| = m − 1 on the range of Theorem 4.10
--   - encoding: real values → values in ℝ≥0∞; reason: the norm may be ∞ a priori
--   - encoding: the set of Simon functions on Z_2^m with nonzero period, and s returning the period → the finite type of pairs (f, s) with s ≠ 0, and the second projection; reason: a nonzero period is unique
--   - encoding: G = Z_2^n with n = r + m → the product (Fin r → ZMod 2) × (Fin m → ZMod 2); reason: Z_2^n ≅ Z_2^r ⊕ Z_2^m as groups; the paper writes G = K ⊕ V itself
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, eq. (60), p.40

import Mathlib
import Definitions.Def_OracleStateHSP_answerNe
import Definitions.Def_OracleStateHSP_relGamma2
import Definitions.Def_OracleStateHSP_SimonInst
import Definitions.Def_OracleStateHSP_fracOracle
open scoped ENNReal

namespace OracleStateHSP

/-- Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, eq. (60), p.40: applying Fact 4.5 with `c = √ε` to the identity (58) gives
`γ₂(1_{s(f)≠s(g)} | (O^ε_f − O^ε_g)_{f,g}) = (1/√ε) γ₂(1_{s(f)≠s(g)} | (O^1_f − O^1_g)_{f,g})
∈ Θ(log |G/H| / √ε)`.

Here: there are universal constants `c, C > 0` such that for every `ε ∈ (0, 1]`, `r ≥ 0` and
`m ≥ 2`, the equality holds and `c (m − 1)/√ε ≤ γ₂(1 | (O^ε_f − O^ε_g)) ≤ C (m − 1)/√ε`.

**Formalization Note.** `Θ` is two constants chosen before `ε`, `r` and `m`; values in `ℝ≥0∞`. -/
theorem eq_60 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ r m : ℕ, 2 ≤ m →
      relGamma2 (answerNe fun x : SimonInst m => x.period)
          (fun x y => fracOracle ε r x.fn - fracOracle ε r y.fn) =
        relGamma2 (answerNe fun x : SimonInst m => x.period)
          (fun x y => fracOracle 1 r x.fn - fracOracle 1 r y.fn) / ENNReal.ofReal (Real.sqrt ε) ∧
      ENNReal.ofReal (c * ((m : ℝ) - 1) / Real.sqrt ε) ≤
          relGamma2 (answerNe fun x : SimonInst m => x.period)
            (fun x y => fracOracle ε r x.fn - fracOracle ε r y.fn) ∧
      relGamma2 (answerNe fun x : SimonInst m => x.period)
          (fun x y => fracOracle ε r x.fn - fracOracle ε r y.fn) ≤
        ENNReal.ofReal (C * ((m : ℝ) - 1) / Real.sqrt ε) := by sorry

end OracleStateHSP
