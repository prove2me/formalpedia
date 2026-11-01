-- Prove2me | Theorems.Thm_OLPRegret_eq_38
-- name    : OLPRegret.eq_38
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:04:34.357972+00:00
-- url     : https://prove2.me/theorems/827d3798-94a7-4f65-9318-1315bcc7ef32
-- title:
--   (38) — the linear and integer benchmarks differ by $O(1)$
-- statement:
--   Under Assumptions 2–6, for a bundle bound $\alpha$:
--
--   1. for every sample with $u_s,a_s\ge0$, $a_s\le\alpha$, if $\beta-m\alpha/n\ge0$ then $V_n^\beta\ge\bar V_n^{\beta-m\alpha/n}$;
--   2. for every sample with $u_s,a_s\ge0$, $\bar V_n^\beta\ge V_n^\beta$;
--   3. there are $C>0$ and $N$ such that for all $n\ge N$ and every policy, $0\le\mathrm E(\underline R_n)-\mathrm E(R_n)\le C$.
--
--   This lets the lower bound work with the linear program rather than the integer program.
--
--   Differences from the source:
--   - encoding: $\mathrm E(\underline R_n)=\mathrm E(R_n)+O(1)$ → $0\le\mathrm E(\underline R_n)-\mathrm E(R_n)\le C$ for $n\ge N$, with $C,N$ before the policy; reason: the difference is $\mathrm E(\bar V_n^\beta)-\mathrm E(V_n^\beta)$, which is nonnegative and independent of the policy
--   - encoding: "almost surely" in Assumptions 2 and 4 → the pathwise clauses are stated for samples satisfying those bounds; reason: samples violating them are null
-- source:
--   Bray, arXiv:1912.08917v6, (38) and the paragraph after it, p.31; $\bar V\ge V$, p.19

import Mathlib
import Definitions.Def_OLPRegret_regret

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Topology

namespace OLPRegret

/-- Bray, arXiv:1912.08917v6, (38), p.31: `E(R̲ₙ) = E(Rₙ) + O(1)`, with the pathwise comparisons
`Vₙᵝ ≥ V̄ₙ^{β−mα/n}` (when `β − mα/n ≥ 0`) and `V̄ₙᵝ ≥ Vₙᵝ` (p.19) that give it.

**Formalization Note** `R̲ₙ − Rₙ = V̄ₙᵝ − Vₙᵝ` does not depend on the policy, so `C` and `N` come before
the policy. -/
theorem eq_38 {m : ℕ} (μ : Measure (Customer m)) [IsProbabilityMeasure μ] (β : E m)
    (hβ : VNonneg β) (hA : Assumptions μ β) (α : E m) (hα : VNonneg α)
    (hαμ : ∀ᵐ z ∂μ, VLe z.2 α) :
    (∀ (n : ℕ) (ω : Sample m n), 1 ≤ n →
      (∀ s, 0 ≤ (ω s).1 ∧ VNonneg (ω s).2 ∧ VLe (ω s).2 α) →
      VNonneg (β - ((m : ℝ) / n) • α) →
      offlineLP ω (β - ((m : ℝ) / n) • α) ≤ offlineIP ω β) ∧
    (∀ (n : ℕ) (ω : Sample m n), (∀ s, 0 ≤ (ω s).1 ∧ VNonneg (ω s).2) →
      offlineIP ω β ≤ offlineLP ω β) ∧
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ π : Policy m n,
      0 ≤ regretLP μ β π - regret μ β π ∧ regretLP μ β π - regret μ β π ≤ C := by sorry

end OLPRegret
