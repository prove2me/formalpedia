-- Prove2me | Theorems.Thm_NoPerfectRandComp_Supplement_theorem_7_5
-- name    : NoPerfectRandComp.Supplement.theorem_7_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:24:19.239714+00:00
-- url     : https://prove2.me/theorems/c49b27a0-d9a8-4458-a6b1-bbe33e9b68e2
-- title:
--   Theorem 7.5 — parity family: $\mathrm{RS}(P_q)=O(m_q)$ and $\chi,\bar\chi,\mathrm{LR},\mathrm{R}$ of $P_q$ all $\Theta(m_q\log q)$
-- statement:
--   **Parity family, sabotage versus conflict.** Throughout, $q$ is odd, $\Gamma$ is the pointer-cell alphabet, $C = C_q$ and $\phi:\{0,1\}^C\to\Gamma$ is a surjective $\lfloor C/3\rfloor$-resilient cell map with $C\le K\,q\log q$ for a fixed $K>0$, $g_q$ is the Blais–Brody block built from $\phi$, $m_q = q^2C$ is its input length and $T_q = \mathrm{R}(g_q)$; $\log$ is $\log_2$. Every $\Theta$, $O$, $\Omega$ has explicit positive constants depending only on $K$ and holds for all odd $q\ge q_0$, for every such $C$ and $\phi$.
--
--   For $P_q = \mathrm{XOR}_q\circ g_q^q$ on $N_q = q\,m_q$ bits,
--   $$
--   \mathrm{RS}(P_q) = O(m_q),\qquad \chi(P_q),\ \bar\chi(P_q),\ \mathrm{LR}(P_q),\ \mathrm{R}(P_q)\ \text{are each}\ \Theta(m_q\log q),
--   $$
--   and hence
--   $$
--   \frac{\chi(P_q)}{\mathrm{RS}(P_q)} = \Omega(\log N_q).
--   $$
--
--   Here $\chi$ and $\bar\chi$ are conflict and max-conflict complexity. On the parity family the whole logarithm between $\mathrm{RS}$ and $\mathrm{R}$ already sits between $\mathrm{RS}$ and $\chi$.
--
--   **Formalization Note** $\chi$, $\bar\chi$, $\mathrm{LR}$, $\mathrm{RS}$ take values in $[0,\infty]$; the ratio is stated as $c\log N_q\cdot\mathrm{RS}(P_q)\le\chi(P_q)$.
--
--   Differences from the source:
--
--   - generalization: g_q built from Blais–Brody's fixed C_q/3-resilient map, C_q = Θ(q log q) → every odd q ≥ q₀, every C ≤ K q log₂ q and every surjective ⌊C/3⌋-resilient ϕ, with constants depending on K only; reason: the paper's map is one admissible ϕ (take K with C_q ≤ K q log q); the proofs use only resilience and C = Θ(q log q), and C ≥ log₂|Γ| ≥ q log₂ q follows from surjectivity
--   - encoding: Θ, O, Ω as family asymptotics in q → explicit constants 0 < c, C and a threshold q₀; ratio clauses multiplied out in ℝ≥0∞; reason: standard reading of the asymptotic notation; a multiplied-out ratio is equivalent because the denominator measure is finite
--   - encoding: N_q, the number of input bits → Fintype.card of the index type of the function; reason: the cardinality is the number of input bits
--   - encoding: zero-error randomised algorithm for h_sab → PMF over finite decision trees on {0,1,∗,†}, correct with probability 1 on every sabotaged input; reason: a zero-error algorithm halts a.s. on the finitely many sabotaged inputs, so cutting each tree below the largest depth reached there changes no cost
--   - reading: χ(P_q) = χ̄(P_q) = LR(P_q) = R(P_q) = Θ(m_q log q) → each of the four measures is between c·m_q log q and C·m_q log q; reason: the proof (p.34) shows each is Θ(m_q log q) via χ ≤ χ̄ ≲ LR ≲ R; it never claims equality
--   - encoding: distributions Q over pairs (χ̄) → discrete distributions (PMF) over pairs; reason: on a finite domain finite mixtures attain the same max-min value (see the definition chiBar)
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Theorem 7.5, p.34 (block g_q: §2.6, p.7)

import Mathlib
import Definitions.Def_NoPerfectRandComp_Reps
import Definitions.Def_NoPerfectRandComp_LR
import Definitions.Def_NoPerfectRandComp_Supplement_IsResilientMap
import Definitions.Def_NoPerfectRandComp_Supplement_Pq
import Definitions.Def_NoPerfectRandComp_Supplement_RS
import Definitions.Def_NoPerfectRandComp_Supplement_chi
import Definitions.Def_NoPerfectRandComp_Supplement_chiBar
open scoped ENNReal

namespace NoPerfectRandComp

namespace Supplement

/-- Theorem 7.5 of Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), p.34 (parity family, sabotage versus conflict): for `k = q`,
`RS(P_q) = O(m_q)` and `χ(P_q) = χ̄(P_q) = LR(P_q) = R(P_q) = Θ(m_q log q)`, and hence
`χ(P_q)/RS(P_q) = Ω(log N_q)`.

**Formalization Note** The family hypothesis is the paper's `C_q = Θ(log |Γ|) = Θ(q log q)` with Blais–Brody's
`⌊C_q/3⌋`-resilient map (§2.6, p.7), which the paper does not reprint: for every `K > 0` the
constants and the threshold depend on `K` only, and the bounds hold for every odd `q ≥ q₀`, every
`C ≤ K q log₂ q` and every surjective `⌊C/3⌋`-resilient `ϕ : {0,1}^C → Γ` (the lower bound
`C ≥ log₂ |Γ| ≥ q log₂ q` follows from surjectivity). `m_q = q² C` and `log` is `log₂`. The chain "`χ = χ̄ = LR = R = Θ(m_q log q)`" asserts that each of
the four measures is `Θ(m_q log q)` (not that they are equal). `N_q = q m_q` is the cardinality of
the index type. `χ`, `χ̄`, `LR`, `RS` are `ℝ≥0∞`-valued; the ratio clause is multiplied out. -/
theorem theorem_7_5 (K : ℝ) (hK : 0 < K) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ q₀ : ℕ, ∀ (q Cq : ℕ) (ϕ : (Fin Cq → Bool) → PtrCell q),
      q₀ ≤ q → Odd q → (Cq : ℝ) ≤ K * q * Real.logb 2 q → IsResilientMap (Cq / 3) ϕ →
        RS (PartialFn.total (Pq q Cq ϕ)) ≤ ENNReal.ofReal (C * ((q ^ 2 * Cq : ℕ) : ℝ)) ∧
        ENNReal.ofReal (c * ((q ^ 2 * Cq : ℕ) : ℝ) * Real.logb 2 q) ≤
          chi (PartialFn.total (Pq q Cq ϕ)) ∧
        chi (PartialFn.total (Pq q Cq ϕ)) ≤
          ENNReal.ofReal (C * ((q ^ 2 * Cq : ℕ) : ℝ) * Real.logb 2 q) ∧
        ENNReal.ofReal (c * ((q ^ 2 * Cq : ℕ) : ℝ) * Real.logb 2 q) ≤
          chiBar (PartialFn.total (Pq q Cq ϕ)) ∧
        chiBar (PartialFn.total (Pq q Cq ϕ)) ≤
          ENNReal.ofReal (C * ((q ^ 2 * Cq : ℕ) : ℝ) * Real.logb 2 q) ∧
        ENNReal.ofReal (c * ((q ^ 2 * Cq : ℕ) : ℝ) * Real.logb 2 q) ≤
          LR (PartialFn.total (Pq q Cq ϕ)) ∧
        LR (PartialFn.total (Pq q Cq ϕ)) ≤
          ENNReal.ofReal (C * ((q ^ 2 * Cq : ℕ) : ℝ) * Real.logb 2 q) ∧
        c * ((q ^ 2 * Cq : ℕ) : ℝ) * Real.logb 2 q ≤ (Rt (Pq q Cq ϕ) : ℝ) ∧
        (Rt (Pq q Cq ϕ) : ℝ) ≤ C * ((q ^ 2 * Cq : ℕ) : ℝ) * Real.logb 2 q ∧
        ENNReal.ofReal
            (c * Real.logb 2 (Fintype.card (Fin q × (Fin q × Fin q × Fin Cq)))) *
          RS (PartialFn.total (Pq q Cq ϕ)) ≤ chi (PartialFn.total (Pq q Cq ϕ)) := by sorry

end Supplement

end NoPerfectRandComp
