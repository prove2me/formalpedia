-- Prove2me | Theorems.Thm_LeaseModular_JointChoice_lemma_3
-- name    : LeaseModular.JointChoice.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:21.127468+00:00
-- url     : https://prove2.me/theorems/52843d01-f11f-49e4-b2f8-1b67c6834b80
-- title:
--   Lemma 3, p. 15 — for each architecture j ∈ {I, M}, leasing is strictly more profitable than selling if γ > 1 or c < C_j
-- statement:
--   Throughout, $\delta_1,\delta_2$ are the module durabilities under selling, $\gamma>0$ the relative return condition of off-lease modules (durabilities under leasing $\delta_{kl}=\gamma\delta_k$), and $c$ the per-module production cost, subject to the standing assumptions $0<\delta_2<\delta_1<1$, $\gamma\delta_1<1$, $0<c<(1-\delta_2)/2$ and $c<(1-\gamma\delta_2)/2$.
--
--   For each product architecture $j\in\{I,M\}$ (integral or modular), the optimal profits exist and leasing is strictly more profitable than selling,
--   $$\Pi^*_{Lj}>\Pi^*_{Sj},$$
--   whenever $\gamma>1$ or $c<C_j(\delta_1,\delta_2,\gamma)$, where $C_I$ and $C_M$ are the thresholds of p. 36 (see the Setting definition).
--
--   When off-lease products are in better condition than used ones, leasing dominates under both architectures; otherwise leasing wins only at low production cost.
--
--   **Formalization Note.** $C_I$ and $C_M$ contain square roots of quantities that are negative for $\gamma>1$, where `Real.sqrt` returns $0$; for $\gamma>1$ the first disjunct already holds, so the value of $C_j$ there is immaterial.
-- source:
--   Agrawal, Atasu & Ülkü, Leasing, Modularity, and the Circular Economy, author manuscript (Management Science, doi:10.1287/mnsc.2020.3829), Lemma 3, p. 15 (proof: Appendix p. 36)

import Mathlib
import Definitions.Def_LeaseModular_JointChoice_Setting

namespace LeaseModular.JointChoice

/-- Lemma 3, p. 15. For each architecture `j ∈ {I, M}`, leasing gives strictly higher optimal
profit than selling (`Π*_Lj > Π*_Sj`) if `γ > 1` or `c < C_j(δ₁, δ₂, γ)`. -/
theorem lemma_3 (P : Params) (hP : Standing P) :
    ∃ vSI vLI vSM vLM : ℝ, IsOptSI P vSI ∧ IsOptLI P vLI ∧ IsOptSM P vSM ∧ IsOptLM P vLM ∧
      ((1 < P.γ ∨ P.c < CI P.δ₁ P.δ₂ P.γ) → vSI < vLI) ∧
      ((1 < P.γ ∨ P.c < CM P.δ₁ P.δ₂ P.γ) → vSM < vLM) := by sorry

end LeaseModular.JointChoice
