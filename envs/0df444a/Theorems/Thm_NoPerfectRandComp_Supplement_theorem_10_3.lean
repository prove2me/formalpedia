-- Prove2me | Theorems.Thm_NoPerfectRandComp_Supplement_theorem_10_3
-- name    : NoPerfectRandComp.Supplement.theorem_10_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:27:17.430205+00:00
-- url     : https://prove2.me/theorems/548b0aff-170c-41e2-bf21-485d79cbe149
-- title:
--   Theorem 10.3 — the block is noise-rigid: $\mathrm{noisyR}_\epsilon(g_q)=\Theta(T_q\log\frac1\epsilon)$ for $1/q\le\epsilon\le1/3$
-- statement:
--   **The block is noise-rigid.** Let $q\ge3$ be odd, $C\le K\,q\log q$ for a fixed $K>0$, $\phi:\{0,1\}^C\to\Gamma$ a surjective $\lfloor C/3\rfloor$-resilient cell map, $g_q$ the Blais–Brody block built from $\phi$ and $T_q = \mathrm{R}(g_q)$. Then
--   $$
--   \mathrm{noisyR}_\epsilon(g_q) = \Theta\Bigl(T_q\log\frac1\epsilon\Bigr)\qquad\Bigl(\frac1q\le\epsilon\le\frac13\Bigr),
--   $$
--   with constants depending only on $K$, uniform in $\epsilon$, $q$, $C$ and $\phi$.
--
--   Here $\mathrm{noisyR}_\epsilon$ is the worst-input expected cost of a noisy-query algorithm with error at most $\epsilon$. Noisy queries do not let an algorithm avoid the $\log(1/\epsilon)$ cost of amplification on the block.
--
--   **Formalization Note** $\log$ is $\log_2$. The paper notes that changing the constants handles the finitely many small parameters, so no threshold beyond $q\ge3$ is imposed; $T_q$ is worst-case depth at error $1/3$, while $\mathrm{noisyR}_\epsilon$ is an expected cost.
--
--   Differences from the source:
--
--   - generalization: g_q built from Blais–Brody's fixed C_q/3-resilient map, C_q = Θ(q log q) → every odd q ≥ 3, every C ≤ K q log₂ q and every surjective ⌊C/3⌋-resilient ϕ, with constants depending on K only; reason: the paper's map is one admissible ϕ; the proof (p.51) uses only ⌊C/3⌋-wise uniformity of the fibres, their density and C = Θ(q log q)
--   - encoding: Θ uniform over 1/q ≤ ε ≤ 1/3 → explicit constants 0 < c, C, the same for all odd q ≥ 3 and all ε in the range; reason: the paper absorbs the finitely many small parameters into the constants (p.52)
--   - encoding: noisy algorithm (randomised, adaptive, correlations γ ∈ [0,1]) → NoisyAlg: an adaptive strategy on histories of answers and fair internal coins, possibly infinite; reason: covers distributions over noisy trees, including a.s.-halting ones; fair coins generate the internal randomness
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Theorem 10.3, p.51 (block g_q and T_q: §2.6, p.7, (5))

import Mathlib
import Definitions.Def_NoPerfectRandComp_Reps
import Definitions.Def_NoPerfectRandComp_Supplement_IsResilientMap
import Definitions.Def_NoPerfectRandComp_Supplement_gq
import Definitions.Def_NoPerfectRandComp_Supplement_noisyReps
open scoped ENNReal

namespace NoPerfectRandComp

namespace Supplement

/-- Theorem 10.3 of Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), p.51 (the block is noise-rigid): for the encoded pointer block
`g_q`, `noisyR_ε(g_q) = Θ(T_q log(1/ε))` for `1/q ≤ ε ≤ 1/3`, where `T_q = R(g_q)` ((5), p.7).

**Formalization Note** The family hypothesis is the paper's `C_q = Θ(log |Γ|) = Θ(q log q)` with Blais–Brody's
`⌊C_q/3⌋`-resilient map (§2.6, p.7), which the paper does not reprint: for every `K > 0` the
constants and the threshold depend on `K` only, and the bounds hold for every odd `q ≥ q₀`, every
`C ≤ K q log₂ q` and every surjective `⌊C/3⌋`-resilient `ϕ : {0,1}^C → Γ` (the lower bound
`C ≥ log₂ |Γ| ≥ q log₂ q` follows from surjectivity). `m_q = q² C` and `log` is `log₂`. The constants are uniform in `ε ∈ [1/q, 1/3]` and hold for every odd
`q ≥ 3` (the paper: "changing the absolute constants handles the finitely many smaller
parameters"). `noisyR_ε` is worst-input expected noisy cost at error `ε` (`ℝ≥0∞`); `T_q` is the
worst-case-depth `R` of the base mission. -/
theorem theorem_10_3 (K : ℝ) (hK : 0 < K) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (q Cq : ℕ) (ϕ : (Fin Cq → Bool) → PtrCell q),
      3 ≤ q → Odd q → (Cq : ℝ) ≤ K * q * Real.logb 2 q → IsResilientMap (Cq / 3) ϕ →
      ∀ ε : ℝ, 1 / (q : ℝ) ≤ ε → ε ≤ 1 / 3 →
        ENNReal.ofReal (c * (Rt (gq q Cq ϕ) : ℝ) * Real.logb 2 (1 / ε)) ≤
            noisyReps ε (PartialFn.total (gq q Cq ϕ)) ∧
          noisyReps ε (PartialFn.total (gq q Cq ϕ)) ≤
            ENNReal.ofReal (C * (Rt (gq q Cq ϕ) : ℝ) * Real.logb 2 (1 / ε)) := by sorry

end Supplement

end NoPerfectRandComp
