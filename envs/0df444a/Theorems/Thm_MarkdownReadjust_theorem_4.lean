-- Prove2me | Theorems.Thm_MarkdownReadjust_theorem_4
-- name    : MarkdownReadjust.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:15:54.275101+00:00
-- url     : https://prove2.me/theorems/e58591f0-9418-43c6-a303-cf1b2227ec15
-- title:
--   Theorem 4 — $N$ markdowns lose $O(k^{1/(N+2)}(\ln k)^{2\alpha}N)$ revenue
-- statement:
--   Fix a model satisfying A1–A3, a horizon $T>0$, an integer inventory $x_0\ge1$ and $\alpha>1/2$. In the $k$-th problem the inventory is $x_0^{(k)}=kx_0$ and the horizon $T^{(k)}=kT$. Use the update times (14) and the shift terms (15). Then there are constants $C_0$ and $K$ such that, for all $k>K$ and every $N\ge1$ with
--
--   $$
--   N\le\max\Big\{0,\ \Big\lfloor\frac{\ln(x_0^{(k)}+1)}{4\alpha\ln\ln(x_0^{(k)}+1)}-2\Big\rfloor\Big\},
--   $$
--
--   the markdown readjustment policy with $N$ price updates satisfies
--
--   $$
--   J^{\pi^{\mathrm{Re}}_\searrow}\big(x_0^{(k)},T^{(k)}\big)\ \ge\ \bar J\big(x_0^{(k)},T^{(k)}\big)-C_0\,k^{\frac1{N+2}}(\ln k)^{2\alpha}N .
--   $$
--
--   So a monotone (markdown) policy with $N$ readjustments loses only $O(k^{1/(N+2)}(\ln k)^{2\alpha}N)$ against the fluid bound $\bar J$, compared with $O(k^{1/2})$ for the fixed price policy.
--
--   Differences from the source:
--   - generalization: valuation c.d.f. F with a density f whose derivative f′ is supported on [0,V), A1–A3 → F̄ continuous and strictly decreasing on [0,V] with F̄(0)=1, F̄(V)=0, plus A2 for R(ρ)=ρF̄⁻¹(ρ) on [0,1], |R| ≤ C on [0,1], and A3's twice differentiability with |R′|, |R″| ≤ C on the open interval (0,1) only; reason: the results use F̄ only through these properties (A1 follows from continuity at V); every model of the paper satisfies them, and nothing is required of R′, R″ at the endpoints ρ = 0, 1
--   - encoding: J^{π}(x₀,T) = E[∫₀ᵀ π_t dY_t] for the continuous-time Poisson arrival process → markdownRevenue: E[Σₙ F̄⁻¹(ρₙ)·min(Dₙ, Xₙ)] under the sequential Poisson law of the interval demand counts Dₙ; reason: Poisson thinning and independent increments: given the past, Dₙ is Poisson(λ(t_{n+1}−tₙ)ρₙ); same value
--   - encoding: J^π ≥ J̄ − O(k^{1/(N+2)}(ln k)^{2α}N) → ∃ Cst K, ∀ k > K, …, J̄ − Cst·k^{1/(N+2)}(ln k)^{2α}N ≤ J^π; reason: definition of O(·) as k → ∞
--   - reading: Fix N ≥ 1 satisfying N ≤ max{0, ⌊ln(x₀+1)/(4α lnln(x₀+1)) − 2⌋} → the condition evaluated at x₀^{(k)} = kx₀, with the constants chosen before k and N (uniform over all admissible N); reason: the proof of Lemma EC.4 (p.ec24) uses the condition at x₀^{(k)} and Corollary 1 lets N grow with k; this is the stronger reading: a fixed N admissible at x₀ is admissible at kx₀ for all large k, so the fixed-N statement follows
-- source:
--   Chen, Jasin, Simple monotonic readjustment policies with applications to markdown pricing and pricing in the presence of strategic customers, SSRN 3740871 (2023-10-09), Theorem 4, p.20

import Mathlib
import Definitions.Def_MarkdownReadjust_Model
import Definitions.Def_MarkdownReadjust_fluidValue
import Definitions.Def_MarkdownReadjust_markdownRevenue
import Definitions.Def_MarkdownReadjust_NCond

namespace MarkdownReadjust

/-- **Theorem 4, p.20** (Chen–Jasin, SSRN 3740871). Fix `α > 1/2` and use the update times (14)
and the shift terms (15). In the asymptotic setting of Theorem 2 (`x₀^{(k)} = k x₀`,
`T^{(k)} = k T`), for `N ≥ 1` satisfying
`N ≤ max{0, ⌊ln(x₀+1)/(4α ln ln(x₀+1)) − 2⌋}`,
`J^{π^Re_↘}(x₀^{(k)}, T^{(k)}) ≥ J̄(x₀^{(k)}, T^{(k)}) − O(k^{1/(N+2)} (ln k)^{2α} N)`.

**Formalization Note.** The `O(·)` is written out: there are constants `Cst` and `K`, depending
only on the model, `T`, `x₀` and `α`, such that the bound holds for all `k > K` and **all**
`N ≥ 1` satisfying the condition, where the condition is evaluated at the k-th inventory
`x₀^{(k)} = k x₀` (uniform in `N`; for a fixed admissible `N` this gives the bound with a fixed
constant). `J^{π^Re_↘}` is `markdownRevenue` (the exact expected revenue of the policy under the
model's Poisson demand) and `J̄` is the fluid value `λTR(ρᵈ)`. `k^{1/(N+2)}` and `(ln k)^{2α}`
are real powers. -/
theorem theorem_4 (M : Model) (T : ℝ) (hT : 0 < T) (x0 : ℕ) (hx0 : 1 ≤ x0) (α : ℝ)
    (hα : 1 / 2 < α) :
    ∃ Cst K : ℝ, ∀ k : ℕ, K < k → ∀ N : ℕ, 1 ≤ N → NCond α N (k * x0) →
      fluidValue M (k * x0) (k * T)
          - Cst * ((k : ℝ) ^ ((1 : ℝ) / ((N : ℝ) + 2)) * Real.log k ^ (2 * α) * N)
        ≤ markdownRevenue M α N (k * x0) (k * T) := by sorry

end MarkdownReadjust
