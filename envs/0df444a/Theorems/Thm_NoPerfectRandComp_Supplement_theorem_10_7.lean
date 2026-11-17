-- Prove2me | Theorems.Thm_NoPerfectRandComp_Supplement_theorem_10_7
-- name    : NoPerfectRandComp.Supplement.theorem_10_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:28:07.079761+00:00
-- url     : https://prove2.me/theorems/3bf8f295-9a02-4ae8-bce1-632380e13a76
-- title:
--   Theorem 10.7 — $H_q=g_q\circ A_q^{m_q}$: $\mathrm{R}(H_q)=\Theta(q^3T_q)$, $\mathrm{R}^*(H_q)=\Theta(q^3T_q\log q)$, $\mathrm{R}^*/\mathrm{R}=\Theta(\log\mathrm{R}(H_q))$
-- statement:
--   **Maximal $\mathrm{R}$ versus $\mathrm{R}^*$, polynomial size.** Throughout, $q$ is odd, $\Gamma$ is the pointer-cell alphabet, $C = C_q$ and $\phi:\{0,1\}^C\to\Gamma$ is a surjective $\lfloor C/3\rfloor$-resilient cell map with $C\le K\,q\log q$ for a fixed $K>0$, $g_q$ is the Blais–Brody block built from $\phi$, $m_q = q^2C$ is its input length and $T_q = \mathrm{R}(g_q)$; $\log$ is $\log_2$. Every $\Theta$, $O$, $\Omega$ has explicit positive constants depending only on $K$ and holds for all odd $q\ge q_0$, for every such $C$ and $\phi$.
--
--   The total function $H_q = g_q\circ A_q^{m_q}$, with $A_q = \mathrm{AND}_{q^2}\circ\mathrm{Maj}_q^{q^2}$, on $N_q = q^3m_q = \Theta(q^6\log q)$ bits satisfies
--   $$
--   \mathrm{R}(H_q) = \Theta(q^3T_q) = \Theta(q^5\log q),\qquad \mathrm{R}^*(H_q) = \Theta(q^3T_q\log q) = \Theta(q^5\log^2 q),
--   $$
--   where $\mathrm{R}^*(f) = \lim_d \mathrm{R}(f^{\circ d})^{1/d}$. Consequently
--   $$
--   \frac{\mathrm{R}^*(H_q)}{\mathrm{R}(H_q)} = \Theta(\log q) = \Theta(\log N_q) = \Theta(\log\mathrm{R}(H_q)).
--   $$
--
--   This shows that the general bound $\mathrm{R}^*(f) = O(\mathrm{R}(f)\log\mathrm{R}(f))$ is tight for total Boolean functions (Corollary 10.8).
--
--   **Formalization Note** Every lower bound on $\mathrm{R}^*(H_q)$ is stated for $\liminf_d\mathrm{R}(H_q^{\circ d})^{1/d}$ and every upper bound for the $\limsup$ (`Rstar`); the ratios are multiplied out.
--
--   Differences from the source:
--
--   - generalization: g_q built from Blais–Brody's fixed C_q/3-resilient map, C_q = Θ(q log q) → every odd q ≥ q₀, every C ≤ K q log₂ q and every surjective ⌊C/3⌋-resilient ϕ, with constants depending on K only; reason: the paper's map is one admissible ϕ (take K with C_q ≤ K q log q); the proofs use only resilience and C = Θ(q log q), and C ≥ log₂|Γ| ≥ q log₂ q follows from surjectivity
--   - encoding: Θ, O, Ω as family asymptotics in q → explicit constants 0 < c, C and a threshold q₀; ratio clauses multiplied out in ℝ≥0∞; reason: standard reading of the asymptotic notation; a multiplied-out ratio is equivalent because the denominator measure is finite
--   - encoding: N_q, the number of input bits → Fintype.card of the index type of the function; reason: the cardinality is the number of input bits
--   - reading: R*(f) = lim_d R(f^∘d)^{1/d} → lower bounds on the liminf, upper bounds on the limsup of R(H_q^∘d)^{1/d}; reason: the paper does not prove that the limit exists; the stronger reading bounds every limit point and gives the printed statement when the limit exists
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Theorem 10.7, p.53 (A_q: Lemma 10.5, p.52; R*: p.4)

import Mathlib
import Definitions.Def_NoPerfectRandComp_Reps
import Definitions.Def_NoPerfectRandComp_Supplement_IsResilientMap
import Definitions.Def_NoPerfectRandComp_Supplement_gq
import Definitions.Def_NoPerfectRandComp_Supplement_Hq
import Definitions.Def_NoPerfectRandComp_Supplement_iterComp
import Definitions.Def_NoPerfectRandComp_Supplement_Rstar
open scoped ENNReal

namespace NoPerfectRandComp

namespace Supplement

/-- Theorem 10.7 of Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), p.53 (maximal R versus R*, polynomial size): the total
function `H_q = g_q ∘ A_q^{m_q}` on `N_q = Θ(q⁶ log q)` bits satisfies
`R(H_q) = Θ(q³ T_q) = Θ(q⁵ log q)` and `R*(H_q) = Θ(q³ T_q log q) = Θ(q⁵ log² q)`, where
`T_q = R(g_q)`. Consequently `R*(H_q)/R(H_q) = Θ(log q) = Θ(log N_q) = Θ(log R(H_q))`.

**Formalization Note** The family hypothesis is the paper's `C_q = Θ(log |Γ|) = Θ(q log q)` with Blais–Brody's
`⌊C_q/3⌋`-resilient map (§2.6, p.7), which the paper does not reprint: for every `K > 0` the
constants and the threshold depend on `K` only, and the bounds hold for every odd `q ≥ q₀`, every
`C ≤ K q log₂ q` and every surjective `⌊C/3⌋`-resilient `ϕ : {0,1}^C → Γ` (the lower bound
`C ≥ log₂ |Γ| ≥ q log₂ q` follows from surjectivity). `m_q = q² C` and `log` is `log₂`. `N_q = q³ m_q` is the cardinality of the index type. The paper's
`R* = lim_d R(H_q^{∘d})^{1/d}`: every lower bound on `R*` is stated for the `liminf` of that
sequence and every upper bound for its `limsup` (`Rstar`), so every limit point obeys the `Θ`.
Ratios are multiplied out (`R(H_q) > 0`). -/
theorem theorem_10_7 (K : ℝ) (hK : 0 < K) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ q₀ : ℕ, ∀ (q Cq : ℕ) (ϕ : (Fin Cq → Bool) → PtrCell q),
      q₀ ≤ q → Odd q → (Cq : ℝ) ≤ K * q * Real.logb 2 q → IsResilientMap (Cq / 3) ϕ →
        c * (q : ℝ) ^ 6 * Real.logb 2 q ≤
            (Fintype.card ((Fin q × Fin q × Fin Cq) × (Fin (q ^ 2) × Fin q)) : ℝ) ∧
          (Fintype.card ((Fin q × Fin q × Fin Cq) × (Fin (q ^ 2) × Fin q)) : ℝ) ≤
            C * (q : ℝ) ^ 6 * Real.logb 2 q ∧
          c * (q : ℝ) ^ 3 * Rt (gq q Cq ϕ) ≤ (Rt (Hq q Cq ϕ) : ℝ) ∧
          (Rt (Hq q Cq ϕ) : ℝ) ≤ C * (q : ℝ) ^ 3 * Rt (gq q Cq ϕ) ∧
          c * (q : ℝ) ^ 5 * Real.logb 2 q ≤ (Rt (Hq q Cq ϕ) : ℝ) ∧
          (Rt (Hq q Cq ϕ) : ℝ) ≤ C * (q : ℝ) ^ 5 * Real.logb 2 q ∧
          c * (q : ℝ) ^ 3 * Rt (gq q Cq ϕ) * Real.logb 2 q ≤
            Filter.liminf (fun d : ℕ => (Rt (iterComp (Hq q Cq ϕ) d) : ℝ) ^ ((1 : ℝ) / d)) Filter.atTop ∧
          Rstar (Hq q Cq ϕ) ≤ C * (q : ℝ) ^ 3 * Rt (gq q Cq ϕ) * Real.logb 2 q ∧
          c * (q : ℝ) ^ 5 * Real.logb 2 q ^ 2 ≤
            Filter.liminf (fun d : ℕ => (Rt (iterComp (Hq q Cq ϕ) d) : ℝ) ^ ((1 : ℝ) / d)) Filter.atTop ∧
          Rstar (Hq q Cq ϕ) ≤ C * (q : ℝ) ^ 5 * Real.logb 2 q ^ 2 ∧
          c * Real.logb 2 q * Rt (Hq q Cq ϕ) ≤
            Filter.liminf (fun d : ℕ => (Rt (iterComp (Hq q Cq ϕ) d) : ℝ) ^ ((1 : ℝ) / d)) Filter.atTop ∧
          Rstar (Hq q Cq ϕ) ≤ C * Real.logb 2 q * Rt (Hq q Cq ϕ) ∧
          c * Real.logb 2 (Fintype.card ((Fin q × Fin q × Fin Cq) × (Fin (q ^ 2) × Fin q))) *
              Rt (Hq q Cq ϕ) ≤
            Filter.liminf (fun d : ℕ => (Rt (iterComp (Hq q Cq ϕ) d) : ℝ) ^ ((1 : ℝ) / d)) Filter.atTop ∧
          Rstar (Hq q Cq ϕ) ≤
            C * Real.logb 2 (Fintype.card ((Fin q × Fin q × Fin Cq) × (Fin (q ^ 2) × Fin q))) *
              Rt (Hq q Cq ϕ) ∧
          c * Real.logb 2 (Rt (Hq q Cq ϕ)) * Rt (Hq q Cq ϕ) ≤
            Filter.liminf (fun d : ℕ => (Rt (iterComp (Hq q Cq ϕ) d) : ℝ) ^ ((1 : ℝ) / d)) Filter.atTop ∧
          Rstar (Hq q Cq ϕ) ≤ C * Real.logb 2 (Rt (Hq q Cq ϕ)) * Rt (Hq q Cq ϕ) := by sorry

end Supplement

end NoPerfectRandComp
