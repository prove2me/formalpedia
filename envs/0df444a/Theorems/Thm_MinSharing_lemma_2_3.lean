-- Prove2me | Theorems.Thm_MinSharing_lemma_2_3
-- name    : MinSharing.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:25:07.021076+00:00
-- url     : https://prove2.me/theorems/a02c03de-605f-4ac9-9a2c-6fec7127aa37
-- title:
--   Lemma 2.3 — fPO iff some positive weights make every consumed object a weighted-value maximizer
-- statement:
--   Let $v$ be an $n\times m$ valuation matrix of arbitrary signs and $z$ an allocation. Then $z$ is fractionally Pareto-optimal if and only if there are weights $\lambda_1,\dots,\lambda_n>0$ such that for all agents $i,j$ and objects $o$,
--   $$z_{i,o}>0\ \Longrightarrow\ \lambda_i v_{i,o}\ \ge\ \lambda_j v_{j,o}. \tag{2.1}$$
--
--   This is the Negishi-type characterization: fPO allocations are exactly the maximizers of a weighted utilitarian welfare with positive weights. It yields the threshold structure of Corollary 2.4 and the reallocation step in the proof of Lemma 3.9.
--
--   Differences from the source:
--   - encoding: z is an allocation → hypothesis IsFeasible z (z ≥ 0, every column sums to 1); reason: the definition of an allocation on p.7
--   - encoding: agents [n] = {1,…,n}, objects [m] = {1,…,m} → Fin n, Fin m (paper index = Lean index + 1); reason: Lean convention; same instances
-- source:
--   Sandomirskiy, Segal-Halevi, Efficient Fair Division with Minimal Sharing, arXiv:1908.01669v3, Lemma 2.3, p.9 (proof Appendix A, pp.29–31)

import Mathlib
import Definitions.Def_CompetitiveChores_RichFamily_Setting

set_option autoImplicit false

namespace MinSharing

open CompetitiveChores.RichFamily

/-- **Lemma 2.3** (Sandomirskiy, Segal-Halevi, arXiv:1908.01669v3, p.9; proof Appendix A,
pp.29–31). An allocation `z` is fractionally Pareto-optimal if and only if there is a vector of
weights `λ = (λᵢ)_{i∈[n]}` with `λᵢ > 0` such that `zᵢ,ₒ > 0` implies `λᵢ vᵢ,ₒ ≥ λⱼ vⱼ,ₒ` (2.1)
for all agents `i, j` and objects `o`.

**Formalization Note** Agents `Fin n`, objects `Fin m`, values of any sign; "an allocation" is
the hypothesis `IsFeasible z`. -/
theorem lemma_2_3 {n m : ℕ} (v z : Fin n → Fin m → ℝ) (hz : IsFeasible z) :
    IsParetoOptimal v z ↔
      ∃ w : Fin n → ℝ, (∀ i, 0 < w i) ∧
        ∀ (i j : Fin n) (o : Fin m), 0 < z i o → w j * v j o ≤ w i * v i o := by sorry

end MinSharing
