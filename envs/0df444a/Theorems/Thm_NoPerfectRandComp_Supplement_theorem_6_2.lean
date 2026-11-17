-- Prove2me | Theorems.Thm_NoPerfectRandComp_Supplement_theorem_6_2
-- name    : NoPerfectRandComp.Supplement.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:23:31.6012+00:00
-- url     : https://prove2.me/theorems/6b761d9c-3434-4ddf-823c-62aa36ae19cd
-- title:
--   Theorem 6.2 — parity family: $\mathrm{RS}(P_q)=O(m_q)$, $\mathrm{R}(P_q)=\Theta(m_q\log q)$, ratio $\Omega(\log N_q)$
-- statement:
--   **Parity family, sabotage versus randomised.** Throughout, $q$ is odd, $\Gamma$ is the pointer-cell alphabet, $C = C_q$ and $\phi:\{0,1\}^C\to\Gamma$ is a surjective $\lfloor C/3\rfloor$-resilient cell map with $C\le K\,q\log q$ for a fixed $K>0$, $g_q$ is the Blais–Brody block built from $\phi$, $m_q = q^2C$ is its input length and $T_q = \mathrm{R}(g_q)$; $\log$ is $\log_2$. Every $\Theta$, $O$, $\Omega$ has explicit positive constants depending only on $K$ and holds for all odd $q\ge q_0$, for every such $C$ and $\phi$.
--
--   Let $P_q = \mathrm{XOR}_q\circ g_q^q$, a total function on $N_q = q\,m_q$ bits. Then $N_q = \Theta(q^4\log q)$ and
--   $$
--   \mathrm{RS}(P_q) = O(m_q),\qquad \mathrm{R}(P_q) = \Theta(m_q\log q),\qquad\text{so}\qquad\frac{\mathrm{R}(P_q)}{\mathrm{RS}(P_q)} = \Omega(\log N_q).
--   $$
--
--   Here $\mathrm{RS}$ is sabotage complexity. There is therefore no constant $c$ with $\mathrm{R}(f)\le c\,\mathrm{RS}(f)$ for all total Boolean $f$ (Corollary 6.3).
--
--   **Formalization Note** $\mathrm{RS}$ takes values in $[0,\infty]$; the ratio is stated as $c\log N_q\cdot\mathrm{RS}(P_q)\le\mathrm{R}(P_q)$.
--
--   Differences from the source:
--
--   - generalization: g_q built from Blais–Brody's fixed C_q/3-resilient map, C_q = Θ(q log q) → every odd q ≥ q₀, every C ≤ K q log₂ q and every surjective ⌊C/3⌋-resilient ϕ, with constants depending on K only; reason: the paper's map is one admissible ϕ (take K with C_q ≤ K q log q); the proofs use only resilience and C = Θ(q log q), and C ≥ log₂|Γ| ≥ q log₂ q follows from surjectivity
--   - encoding: Θ, O, Ω as family asymptotics in q → explicit constants 0 < c, C and a threshold q₀; ratio clauses multiplied out in ℝ≥0∞; reason: standard reading of the asymptotic notation; a multiplied-out ratio is equivalent because the denominator measure is finite
--   - encoding: N_q, the number of input bits → Fintype.card of the index type of the function; reason: the cardinality is the number of input bits
--   - encoding: zero-error randomised algorithm for h_sab → PMF over finite decision trees on {0,1,∗,†}, correct with probability 1 on every sabotaged input; reason: a zero-error algorithm halts a.s. on the finitely many sabotaged inputs, so cutting each tree below the largest depth reached there changes no cost
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Theorem 6.2, p.29 (block g_q: §2.6, p.7)

import Mathlib
import Definitions.Def_NoPerfectRandComp_Reps
import Definitions.Def_NoPerfectRandComp_Supplement_IsResilientMap
import Definitions.Def_NoPerfectRandComp_Supplement_Pq
import Definitions.Def_NoPerfectRandComp_Supplement_RS
open scoped ENNReal

namespace NoPerfectRandComp

namespace Supplement

/-- Theorem 6.2 of Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), p.29 (parity family, sabotage versus randomised):
`P_q = XOR_q ∘ g_q^q` is a total function on `N_q = q m_q = Θ(q⁴ log q)` bits with
`RS(P_q) = O(m_q)`, `R(P_q) = Θ(m_q log q)`, so `R(P_q)/RS(P_q) = Ω(log N_q)`.

**Formalization Note** The family hypothesis is the paper's `C_q = Θ(log |Γ|) = Θ(q log q)` with Blais–Brody's
`⌊C_q/3⌋`-resilient map (§2.6, p.7), which the paper does not reprint: for every `K > 0` the
constants and the threshold depend on `K` only, and the bounds hold for every odd `q ≥ q₀`, every
`C ≤ K q log₂ q` and every surjective `⌊C/3⌋`-resilient `ϕ : {0,1}^C → Γ` (the lower bound
`C ≥ log₂ |Γ| ≥ q log₂ q` follows from surjectivity). `m_q = q² C` and `log` is `log₂`. `N_q` is the cardinality of the index type `[q] × ([q] × [q] × [C])`.
`RS` is valued in `ℝ≥0∞`; the ratio clause is multiplied out. -/
theorem theorem_6_2 (K : ℝ) (hK : 0 < K) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ q₀ : ℕ, ∀ (q Cq : ℕ) (ϕ : (Fin Cq → Bool) → PtrCell q),
      q₀ ≤ q → Odd q → (Cq : ℝ) ≤ K * q * Real.logb 2 q → IsResilientMap (Cq / 3) ϕ →
        c * (q : ℝ) ^ 4 * Real.logb 2 q ≤
            (Fintype.card (Fin q × (Fin q × Fin q × Fin Cq)) : ℝ) ∧
          (Fintype.card (Fin q × (Fin q × Fin q × Fin Cq)) : ℝ) ≤
            C * (q : ℝ) ^ 4 * Real.logb 2 q ∧
          RS (PartialFn.total (Pq q Cq ϕ)) ≤ ENNReal.ofReal (C * ((q ^ 2 * Cq : ℕ) : ℝ)) ∧
          c * ((q ^ 2 * Cq : ℕ) : ℝ) * Real.logb 2 q ≤ (Rt (Pq q Cq ϕ) : ℝ) ∧
          (Rt (Pq q Cq ϕ) : ℝ) ≤ C * ((q ^ 2 * Cq : ℕ) : ℝ) * Real.logb 2 q ∧
          ENNReal.ofReal
              (c * Real.logb 2 (Fintype.card (Fin q × (Fin q × Fin q × Fin Cq)))) *
            RS (PartialFn.total (Pq q Cq ϕ)) ≤ (Rt (Pq q Cq ϕ) : ℝ≥0∞) := by sorry

end Supplement

end NoPerfectRandComp
