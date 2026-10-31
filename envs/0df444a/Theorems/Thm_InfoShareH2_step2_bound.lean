-- Prove2me | Theorems.Thm_InfoShareH2_step2_bound
-- name    : InfoShareH2.step2_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:30:29.114253+00:00
-- url     : https://prove2.me/theorems/85c24247-18b0-44d2-832b-18c707f3c7cf
-- title:
--   §9.7 Step 2 — $\tilde C_Q\ge(5-2\log2\sigma)/4$, with equality at $Q^\star=(1+z)/2$
-- statement:
--   Normalize $\sigma_\epsilon=1$ and let $\sigma>0$. For every outer function $Q(z)=\sum_nq_nz^n$ with real coefficients $q\in\tilde\Psi$ satisfying Assumption 2,
--
--   $$\tilde C_Q=\frac12\log|q_0|+S_1(Q)-\frac12\log\sigma\ \ge\ \frac{5-2\log2\sigma}{4}.$$
--
--   The bound is attained: $Q^\star(z)=(1+z)/2$ (coefficients $(\tfrac12,\tfrac12,0,\dots)$) is such a function, $S_1(Q^\star)=5/4$, and $\tilde C_{Q^\star}=(5-2\log2\sigma)/4$. Moreover, for $\sigma\in(0,\tfrac12]$ the pair $Q^\star$, $\gamma^\star=-\log(2\sigma)$ (the singular factor $G^\star(z)=\exp(\gamma^\star\frac{z-1}{z+1})$) is feasible for (40), i.e. $\gamma^\star\ge0$ and $Q^\star(0)^2e^{-2\gamma^\star}\le\sigma^2$, and its objective $S_1(Q^\star)+\gamma^\star/2$ equals $(5-2\log2\sigma)/4$.
--
--   This is where the constants of Theorem 2 come from: with $\sigma_\epsilon$ restored, $\frac{5-2\log 2\sigma}{4}$ becomes $\frac{\sigma_\epsilon^2}4\bigl(5-\log\frac{4\sigma^2}{\sigma_\epsilon^2}\bigr)$.
--
--   Differences from the source:
--   - encoding: σ_ε = 1 (§9.7) → σ_ε = 1 throughout; reason: the normalization of §9.7
--   - reading: C̃_Q over the class of (40) "Q ∈ H²_O ∩ Ψ̃" under Assumption 2 → q ∈ Ψ̃ real, (q_n) outer, Assumption 2 for q; reason: the class over which Step 2 minimizes
--   - reading: "the inequality in (40) becomes an equality when σ ∈ (0, 1/2] and Q⋆, G⋆, γ⋆" → Q⋆ is in the class with C̃_{Q⋆} equal to the bound; for σ ≤ 1/2, (Q⋆, γ⋆) is feasible for (40) with objective equal to the bound; reason: the printed equality case, made explicit
--   - encoding: S1(Q) + real terms ≥ bound → ENNReal.ofReal(bound − ½log|q₀| + ½log σ) ≤ S1(Q) in [0, ∞]; reason: S1 may a priori be infinite; equivalent to the printed inequality
-- source:
--   Caldentey–Giloni–Hurvich–Zhang, Information Design and Sharing in Supply Chains, SSRN 4319721 (v. 2024-01-20), https://ssrn.com/abstract=4319721, §9.7 Step 2, final display, p.44 (unnumbered); (40)–(41) p.27, (46) p.43

import Mathlib
import Definitions.Def_InfoShareH2_Model
import Definitions.Def_InfoShareH2_Hardy

open Filter Topology MeasureTheory Complex

set_option autoImplicit false

namespace InfoShareH2

/-- **§9.7 Step 2: `C̃_Q ≥ (5 − 2 log 2σ)/4`, attained at `Q⋆ = (1 + z)/2`.**
SSRN 4319721 (v. 2024-01-20), §9.7 Step 2, final display, p.44 (unnumbered; σ_ε = 1 as in §9.7):
"`C̃_Q = (1/2) log |Q_0| + S1(Q) − (1/2) log σ ≥ (5 − 2 log 2σ)/4`, where the inequality in (40)
becomes an equality when `σ ∈ (0, 1/2]` and `Q⋆(z) = (1 + z)/2`, `G⋆(z) = exp(γ⋆ (z − 1)/(z + 1))`, and
`γ⋆ = −log(2σ)`."

The class is that of (40) under Assumption 2: `Q` has real coefficients `q ∈ Ψ̃`, is outer, and
satisfies Assumption 2 (`Q_0 = Q(0) = q_0`). The equality part says: `Q⋆ = (1 + z)/2` (coefficients
`(1/2, 1/2, 0, …)`) lies in this class with `C̃_{Q⋆}` equal to the bound, and for `σ ∈ (0, 1/2]`,
`(Q⋆, γ⋆)` is feasible for (40) (`Q⋆(0)² e^{−2γ⋆} ≤ σ²`, `γ⋆ ≥ 0`) with objective
`S1(Q⋆) + γ⋆/2` equal to the bound.

**Formalization Note** `S1` takes values in `ℝ≥0∞`; the inequality is written as
`ENNReal.ofReal (bound − (1/2) log |q_0| + (1/2) log σ) ≤ S1(Q)`, which is equivalent to the printed
one (it holds trivially when `S1(Q) = ∞`). -/
theorem step2_bound (σ : ℝ) (hσ : 0 < σ) :
    let qstar : ℕ → ℝ := fun n => if n ≤ 1 then 1 / 2 else 0
    let γstar : ℝ := -Real.log (2 * σ)
    (∀ q : ℕ → ℝ, q ∈ PsiTilde → IsOuter (ofRealSeq q) → Assumption2 q →
      ENNReal.ofReal ((5 - 2 * Real.log (2 * σ)) / 4 - (1 / 2) * Real.log |q 0| + (1 / 2) * Real.log σ)
        ≤ S1 (zTransform (ofRealSeq q))) ∧
    qstar ∈ PsiTilde ∧ IsOuter (ofRealSeq qstar) ∧ Assumption2 qstar ∧
    S1 (zTransform (ofRealSeq qstar)) = ENNReal.ofReal (5 / 4) ∧
    (1 / 2) * Real.log |qstar 0| + 5 / 4 - (1 / 2) * Real.log σ = (5 - 2 * Real.log (2 * σ)) / 4 ∧
    (σ ≤ 1 / 2 → 0 ≤ γstar ∧ qstar 0 ^ 2 * Real.exp (-2 * γstar) ≤ σ ^ 2 ∧
      5 / 4 + γstar / 2 = (5 - 2 * Real.log (2 * σ)) / 4) := by sorry

end InfoShareH2
