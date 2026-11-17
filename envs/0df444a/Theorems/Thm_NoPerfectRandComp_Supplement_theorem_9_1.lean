-- Prove2me | Theorems.Thm_NoPerfectRandComp_Supplement_theorem_9_1
-- name    : NoPerfectRandComp.Supplement.theorem_9_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:26:07.178471+00:00
-- url     : https://prove2.me/theorems/157d584d-86e0-4cc5-9980-5ec9a30fcffd
-- title:
--   Theorem 9.1 — AND of ORs: $\mathrm{RS}(F_m),\bar\chi(F_m)=\Theta(m^2)$, $\Omega(m^2/\log^2m)=\chi(F_m)=O(m^2/\sqrt{\log m})$
-- statement:
--   **AND of ORs.** For $F_m = \mathrm{AND}_m\circ\mathrm{OR}_m$ on $N = m^2$ bits,
--   $$
--   \mathrm{RS}(F_m) = \Theta(m^2),\qquad \bar\chi(F_m) = \Theta(m^2),\qquad \Omega\Bigl(\frac{m^2}{\log^2 m}\Bigr) = \chi(F_m) = O\Bigl(\frac{m^2}{\sqrt{\log m}}\Bigr).
--   $$
--   In particular $\chi(F_m) = o(\mathrm{RS}(F_m))$, and
--   $$
--   \frac{\bar\chi(F_m)}{\chi(F_m)} = \Omega\bigl(\sqrt{\log N}\bigr).
--   $$
--
--   Together with Theorem 7.5 this makes $\mathrm{RS}$ and $\chi$ incomparable on total functions, and it separates $\chi$ from $\bar\chi$.
--
--   **Formalization Note** $\log$ is $\log_2$; the bounds have explicit constants and hold for $m\ge m_0$. $\chi(F_m) = o(\mathrm{RS}(F_m))$ is $\chi(F_m)/\mathrm{RS}(F_m)\to0$ in $[0,\infty]$, and the last ratio is stated as $c\sqrt{\log N}\cdot\chi(F_m)\le\bar\chi(F_m)$.
--
--   Differences from the source:
--
--   - encoding: Θ, O, Ω in m (base-free logarithms) → explicit constants 0 < c, C, a threshold m₀, log₂; the last ratio multiplied out in ℝ≥0∞; reason: standard reading; the base of the logarithm changes only constants, and χ(F_m) is finite
--   - encoding: χ(F_m) = o(RS(F_m)) → Tendsto (χ(F_m)/RS(F_m)) atTop (𝓝 0) in ℝ≥0∞; reason: definition of little-o for positive quantities
--   - encoding: N_q, the number of input bits → Fintype.card of the index type of the function; reason: the cardinality is the number of input bits
--   - encoding: zero-error randomised algorithm for h_sab → PMF over finite decision trees on {0,1,∗,†}, correct with probability 1 on every sabotaged input; reason: a zero-error algorithm halts a.s. on the finitely many sabotaged inputs, so cutting each tree below the largest depth reached there changes no cost
--   - encoding: distributions Q over pairs (χ̄) → discrete distributions (PMF) over pairs; reason: on a finite domain finite mixtures attain the same max-min value (see the definition chiBar)
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Theorem 9.1, p.38 (F_m: §9, p.37)

import Mathlib
import Definitions.Def_NoPerfectRandComp_PartialFn
import Definitions.Def_NoPerfectRandComp_Supplement_Fm
import Definitions.Def_NoPerfectRandComp_Supplement_RS
import Definitions.Def_NoPerfectRandComp_Supplement_chi
import Definitions.Def_NoPerfectRandComp_Supplement_chiBar
open scoped ENNReal

namespace NoPerfectRandComp

namespace Supplement

/-- Theorem 9.1 of Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), p.38 (AND of ORs): for `F_m = AND_m ∘ OR_m` on `N = m²` bits,
`RS(F_m) = Θ(m²)`, `χ̄(F_m) = Θ(m²)`, `Ω(m²/log² m) = χ(F_m) = O(m²/√(log m))`. In particular
`χ(F_m) = o(RS(F_m))`, and `χ̄(F_m)/χ(F_m) = Ω(√(log N))`.

**Formalization Note** The `Θ`, `O`, `Ω` clauses have explicit constants `c, C > 0` and a
threshold `m₀`; `log` is `log₂` (the bounds are base-free up to constants). "`Ω(m²/log² m) = χ(F_m)`"
is the lower bound `c m²/(log m)² ≤ χ(F_m)`. `χ = o(RS)` is `χ(F_m)/RS(F_m) → 0` in `ℝ≥0∞`;
`N = m²` is the cardinality of `[m] × [m]`; the last ratio is multiplied out. -/
theorem theorem_9_1 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ m₀ : ℕ,
      (∀ m : ℕ, m₀ ≤ m →
        ENNReal.ofReal (c * (m : ℝ) ^ 2) ≤ RS (PartialFn.total (Fm m)) ∧
        RS (PartialFn.total (Fm m)) ≤ ENNReal.ofReal (C * (m : ℝ) ^ 2) ∧
        ENNReal.ofReal (c * (m : ℝ) ^ 2) ≤ chiBar (PartialFn.total (Fm m)) ∧
        chiBar (PartialFn.total (Fm m)) ≤ ENNReal.ofReal (C * (m : ℝ) ^ 2) ∧
        ENNReal.ofReal (c * (m : ℝ) ^ 2 / Real.logb 2 m ^ 2) ≤ chi (PartialFn.total (Fm m)) ∧
        chi (PartialFn.total (Fm m)) ≤
          ENNReal.ofReal (C * (m : ℝ) ^ 2 / Real.sqrt (Real.logb 2 m)) ∧
        ENNReal.ofReal (c * Real.sqrt (Real.logb 2 (Fintype.card (Fin m × Fin m)))) *
          chi (PartialFn.total (Fm m)) ≤ chiBar (PartialFn.total (Fm m))) ∧
      Filter.Tendsto (fun m : ℕ => chi (PartialFn.total (Fm m)) / RS (PartialFn.total (Fm m)))
        Filter.atTop (nhds 0) := by sorry

end Supplement

end NoPerfectRandComp
