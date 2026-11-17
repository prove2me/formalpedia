-- Prove2me | Theorems.Thm_NoPerfectRandComp_Supplement_theorem_8_3
-- name    : NoPerfectRandComp.Supplement.theorem_8_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:25:07.587194+00:00
-- url     : https://prove2.me/theorems/147926c4-2112-4925-bdab-a10271413fac
-- title:
--   Theorem 8.3 — masked family: $\mathrm{RS},\bar\chi=\Theta(m_q)$, $\mathrm{R}=\Theta(m_q\log q)$, $\Omega(m_q\sqrt{\log q})\le\mathrm{LR}(G_q)\le O(m_q\log q)$
-- statement:
--   **Masked family, max-conflict versus linearised.** Throughout, $q$ is odd, $\Gamma$ is the pointer-cell alphabet, $C = C_q$ and $\phi:\{0,1\}^C\to\Gamma$ is a surjective $\lfloor C/3\rfloor$-resilient cell map with $C\le K\,q\log q$ for a fixed $K>0$, $g_q$ is the Blais–Brody block built from $\phi$, $m_q = q^2C$ is its input length and $T_q = \mathrm{R}(g_q)$; $\log$ is $\log_2$. Every $\Theta$, $O$, $\Omega$ has explicit positive constants depending only on $K$ and holds for all odd $q\ge q_0$, for every such $C$ and $\phi$. In addition $t = t_q$ satisfies $c_1m_q\le t\le c_2m_q$ for fixed $c_1, c_2 > 0$ (that is, $t = \Theta(m_q)$), and the constants depend on $K, c_1, c_2$ only.
--
--   Let $G_q(x,z) = M_q(x)\oplus\mathrm{XOR}_t(z)$, a total function on $N_q = q\,m_q + t$ bits. Then $N_q = \Theta(q^4\log q)$,
--   $$
--   \mathrm{RS}(G_q) = \Theta(m_q),\qquad \bar\chi(G_q) = \Theta(m_q),\qquad \mathrm{R}(G_q) = \Theta(m_q\log q),
--   $$
--   $$
--   \Omega\bigl(m_q\sqrt{\log q}\bigr)\ \le\ \mathrm{LR}(G_q)\ \le\ O(m_q\log q),
--   $$
--   and hence $\mathrm{LR}(G_q)/\bar\chi(G_q) = \Omega\bigl(\sqrt{\log N_q}\bigr)$.
--
--   This separates max-conflict complexity from linearised complexity on a total function.
--
--   **Formalization Note** The measures take values in $[0,\infty]$; the ratio is stated as $c\sqrt{\log N_q}\cdot\bar\chi(G_q)\le\mathrm{LR}(G_q)$.
--
--   Differences from the source:
--
--   - generalization: g_q built from Blais–Brody's fixed C_q/3-resilient map, C_q = Θ(q log q) → every odd q ≥ q₀, every C ≤ K q log₂ q and every surjective ⌊C/3⌋-resilient ϕ, with constants depending on K only; reason: the paper's map is one admissible ϕ (take K with C_q ≤ K q log q); the proofs use only resilience and C = Θ(q log q), and C ≥ log₂|Γ| ≥ q log₂ q follows from surjectivity
--   - encoding: Θ, O, Ω as family asymptotics in q → explicit constants 0 < c, C and a threshold q₀; ratio clauses multiplied out in ℝ≥0∞; reason: standard reading of the asymptotic notation; a multiplied-out ratio is equivalent because the denominator measure is finite
--   - encoding: N_q, the number of input bits → Fintype.card of the index type of the function; reason: the cardinality is the number of input bits
--   - encoding: zero-error randomised algorithm for h_sab → PMF over finite decision trees on {0,1,∗,†}, correct with probability 1 on every sabotaged input; reason: a zero-error algorithm halts a.s. on the finitely many sabotaged inputs, so cutting each tree below the largest depth reached there changes no cost
--   - reading: t = Θ(m_q) → hypothesis c₁·m_q ≤ t ≤ c₂·m_q for arbitrary c₁, c₂ > 0, constants depending on K, c₁, c₂; reason: the standard reading of a Θ hypothesis on a family t_q; it covers every family t = Θ(m_q)
--   - reading: RS(G_q) = χ̄(G_q) = Θ(m_q) → each of RS(G_q) and χ̄(G_q) is between c·m_q and C·m_q; reason: the proof (p.37) pins each to Θ(m_q); equality is not claimed
--   - encoding: distributions Q over pairs (χ̄) → discrete distributions (PMF) over pairs; reason: on a finite domain finite mixtures attain the same max-min value (see the definition chiBar)
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Theorem 8.3, p.37 (M_q: Theorem 3.5, p.10)

import Mathlib
import Definitions.Def_NoPerfectRandComp_Reps
import Definitions.Def_NoPerfectRandComp_LR
import Definitions.Def_NoPerfectRandComp_Supplement_IsResilientMap
import Definitions.Def_NoPerfectRandComp_Supplement_Gq__febc63
import Definitions.Def_NoPerfectRandComp_Supplement_RS
import Definitions.Def_NoPerfectRandComp_Supplement_chiBar
open scoped ENNReal

namespace NoPerfectRandComp

namespace Supplement

/-- Theorem 8.3 of Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), p.37 (masked family, max-conflict versus linearised): let
`t = Θ(m_q)` and `G_q(x, z) = M_q(x) ⊕ XOR_t(z)`, a total function on `N_q = Θ(q⁴ log q)` bits.
Then `RS(G_q) = χ̄(G_q) = Θ(m_q)`, `R(G_q) = Θ(m_q log q)`,
`Ω(m_q √(log q)) ≤ LR(G_q) ≤ O(m_q log q)`, and hence `LR(G_q)/χ̄(G_q) = Ω(√(log N_q))`.

**Formalization Note** The family hypothesis is the paper's `C_q = Θ(log |Γ|) = Θ(q log q)` with Blais–Brody's
`⌊C_q/3⌋`-resilient map (§2.6, p.7), which the paper does not reprint: for every `K > 0` the
constants and the threshold depend on `K` only, and the bounds hold for every odd `q ≥ q₀`, every
`C ≤ K q log₂ q` and every surjective `⌊C/3⌋`-resilient `ϕ : {0,1}^C → Γ` (the lower bound
`C ≥ log₂ |Γ| ≥ q log₂ q` follows from surjectivity). `m_q = q² C` and `log` is `log₂`. `t = Θ(m_q)` is the hypothesis `c₁ m_q ≤ t ≤ c₂ m_q`, and the
constants depend on `K, c₁, c₂` only. "`RS = χ̄ = Θ(m_q)`" asserts that each is `Θ(m_q)`.
`N_q = q m_q + t` is the cardinality of the index type `([q] × ([q] × [q] × [C])) ⊕ [t]`. The `LR`
lower bound is `m_q √(log q)` (p.37's proof: `Ω(√(t · R(M_q))) = Ω(m_q √(log q))`). Ratios are
multiplied out in `ℝ≥0∞`. -/
theorem theorem_8_3 (K c₁ c₂ : ℝ) (hK : 0 < K) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ q₀ : ℕ, ∀ (q Cq t : ℕ) (ϕ : (Fin Cq → Bool) → PtrCell q),
      q₀ ≤ q → Odd q → (Cq : ℝ) ≤ K * q * Real.logb 2 q → IsResilientMap (Cq / 3) ϕ →
      c₁ * ((q ^ 2 * Cq : ℕ) : ℝ) ≤ t → (t : ℝ) ≤ c₂ * ((q ^ 2 * Cq : ℕ) : ℝ) →
        c * (q : ℝ) ^ 4 * Real.logb 2 q ≤
            (Fintype.card ((Fin q × (Fin q × Fin q × Fin Cq)) ⊕ Fin t) : ℝ) ∧
          (Fintype.card ((Fin q × (Fin q × Fin q × Fin Cq)) ⊕ Fin t) : ℝ) ≤
            C * (q : ℝ) ^ 4 * Real.logb 2 q ∧
          ENNReal.ofReal (c * ((q ^ 2 * Cq : ℕ) : ℝ)) ≤ RS (PartialFn.total (Gq q Cq ϕ t)) ∧
          RS (PartialFn.total (Gq q Cq ϕ t)) ≤ ENNReal.ofReal (C * ((q ^ 2 * Cq : ℕ) : ℝ)) ∧
          ENNReal.ofReal (c * ((q ^ 2 * Cq : ℕ) : ℝ)) ≤
            chiBar (PartialFn.total (Gq q Cq ϕ t)) ∧
          chiBar (PartialFn.total (Gq q Cq ϕ t)) ≤
            ENNReal.ofReal (C * ((q ^ 2 * Cq : ℕ) : ℝ)) ∧
          c * ((q ^ 2 * Cq : ℕ) : ℝ) * Real.logb 2 q ≤ (Rt (Gq q Cq ϕ t) : ℝ) ∧
          (Rt (Gq q Cq ϕ t) : ℝ) ≤ C * ((q ^ 2 * Cq : ℕ) : ℝ) * Real.logb 2 q ∧
          ENNReal.ofReal (c * ((q ^ 2 * Cq : ℕ) : ℝ) * Real.sqrt (Real.logb 2 q)) ≤
            LR (PartialFn.total (Gq q Cq ϕ t)) ∧
          LR (PartialFn.total (Gq q Cq ϕ t)) ≤
            ENNReal.ofReal (C * ((q ^ 2 * Cq : ℕ) : ℝ) * Real.logb 2 q) ∧
          ENNReal.ofReal (c * Real.sqrt (Real.logb 2
              (Fintype.card ((Fin q × (Fin q × Fin q × Fin Cq)) ⊕ Fin t)))) *
            chiBar (PartialFn.total (Gq q Cq ϕ t)) ≤
              LR (PartialFn.total (Gq q Cq ϕ t)) := by sorry

end Supplement

end NoPerfectRandComp
