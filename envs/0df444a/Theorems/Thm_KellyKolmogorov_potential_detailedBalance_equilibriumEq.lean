-- Prove2me | Theorems.Thm_KellyKolmogorov_potential_detailedBalance_equilibriumEq
-- name    : KellyKolmogorov.potential_detailedBalance_equilibriumEq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:44:08.37412+00:00
-- url     : https://prove2.me/theorems/d2f75a44-e1e8-4a97-8d34-7efd6db21d36
-- title:
--   Proof of Theorem 1.7 — the potential satisfies detailed balance and the equilibrium equations
-- statement:
--   Let $\mathcal S$ be a set and $w(j,k)\ge0$ nonnegative weights satisfying Kolmogorov's cycle condition. Fix a reference state $j_0$ and a constant $B>0$, and let $m(j)$, $j\in\mathcal S$, be given by
--   $$
--   m(j)=B\,\frac{\text{product of } w \text{ along } l_j \text{ reversed}}{\text{product of } w \text{ along } l_j}
--   $$
--   for some finite sequence $l_j$ leading from $j$ to $j_0$ with positive forward product (one for each $j$). Then
--
--   1. $m$ satisfies the detailed balance conditions $m(j)w(j,k)=m(k)w(k,j)$ for all $j,k$;
--   2. $m$ satisfies the equilibrium equations $m(j)\sum_k w(j,k)=\sum_k m(k)w(k,j)$ for all $j$.
--
--   Differences from the source:
--   - generalization: the detailed balance and equilibrium properties of π(j) stated for the transition probabilities p of a Markov chain (proof of Theorem 1.7) → stated for arbitrary nonnegative weights w : 𝒮 → 𝒮 → ℝ≥0; reason: the step uses only the algebra of the products; it specializes to w = p verbatim and to w = q, the 'direct analogue' for a Markov process used by Theorem 1.8 (p. 23)
--   - encoding: a sequence of states j, jn, …, j1, j0 leading from j to j0 and the products p(j, jn)⋯p(j1, j0), p(j0, j1)⋯p(jn, j) → a list l with IsPathFromTo l j j₀, fwdProd w l and revProd w l; reason: lists of states with first and last element fixed; same instances
--   - generalization: the equilibrium equations (1.1) of a chain → the equilibrium equations in the rate form (1.3) for w; reason: for the rates q this is (1.3), the analogue Theorem 1.8 uses; for a stochastic matrix p (rows summing to 1) it is (1.1)
--   - encoding: the sums in the equilibrium equations → computed in ℝ≥0∞ with ENNReal.ofReal (m j); reason: every term is nonnegative, so the extended sums are the book's sums and cannot be junk
--   - encoding: π(j) defined from a chosen sequence for each j → any m with, for each j, some sequence from j to j₀ giving m j = B · revProd / fwdProd; reason: covers every choice of sequences; same instances
-- source:
--   Kelly, Reversibility and Stochastic Networks (Wiley 1979), proof of Theorem 1.7, p. 22 (PDF p. 25)

import Mathlib
import Definitions.Def_KellyKolmogorov_KolmogorovCycle
import Definitions.Def_KellyKolmogorov_fwdProd
import Definitions.Def_KellyKolmogorov_revProd
import Definitions.Def_KellyKolmogorov_IsPathFromTo
import Definitions.Def_KellyKolmogorov_DetailedBalance
import Definitions.Def_KellyKolmogorov_EquilibriumEq

open scoped NNReal

namespace KellyKolmogorov

/-- **The potential satisfies detailed balance and the equilibrium equations.**
Kelly, *Reversibility and Stochastic Networks* (Wiley 1979), proof of Theorem 1.7, p. 22: "Thus
`π(j)`, `j ∈ 𝒮`, satisfy the detailed balance conditions and so they also satisfy the
equilibrium equations."

Let `w` be nonnegative weights satisfying Kolmogorov's cycle condition, `j₀` a reference state,
`B > 0`, and `m(j) = B · revProd w l / fwdProd w l` for some sequence `l` from `j` to `j₀` with
positive forward product (one for each `j`). Then `m` satisfies the detailed balance conditions
and the equilibrium equations (1.3) for `w`. -/
theorem potential_detailedBalance_equilibriumEq {𝒮 : Type*} (w : 𝒮 → 𝒮 → ℝ≥0)
    (hw : KolmogorovCycle w) (j₀ : 𝒮) (B : ℝ) (hB : 0 < B) (m : 𝒮 → ℝ)
    (hm : ∀ j, ∃ l : List 𝒮, IsPathFromTo l j j₀ ∧ 0 < fwdProd w l ∧
      m j = B * (revProd w l : ℝ) / (fwdProd w l : ℝ)) :
    DetailedBalance m w ∧ EquilibriumEq m w := by sorry

end KellyKolmogorov
