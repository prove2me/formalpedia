-- Prove2me | Theorems.Thm_MNLStability_theorem_3
-- name    : MNLStability.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:32:16.317979+00:00
-- url     : https://prove2.me/theorems/1cfe95c0-7e6a-42c0-b9d3-db5261179d19
-- title:
--   Theorem 3 — compact $I$-universal families, constructed explicitly (corrected: no $\log\Delta$ factor)
-- statement:
--   There are absolute constants $c_1,c_2>0$ with the following property. For every $n\ge1$, every capacity $C\ge1$, every non-negative prices, every set of products $I$ listed by non-increasing price, and every $\varepsilon>0$, every run of the program `family` returns a list $\mathcal U_I$ such that:
--
--   1. $|\mathcal U_I|\le c_1\,(nC)^{c_2/\varepsilon^2}$;
--   2. the run costs at most $c_1\,(nC)^{c_2/\varepsilon^2}$ unit operations;
--   3. $\mathcal U_I$ is $I$-universal with accuracy $\varepsilon$ for every positive preference weights that are uniform on $I$ and every finitely supported law of the number of customers $M$.
--
--   The paper states an $I$-universal set of $O((nC)^{O(1/\varepsilon^2)}\cdot\log\Delta)$ vectors constructed in the same time. Gluing one family per weight class is the enumeration behind Theorem 1.
--
--   Differences from the source:
--   - correction: size and time O((nC)^{O(1/ε²)} · log Δ) → c₁·(nC)^{c₂/ε²}, with no log Δ factor; reason: the printed bound is 0 when Δ = 1 (all weights equal, as in §6.1), while an I-universal set is nonempty (U = 0 needs a member) and its construction costs at least one operation
--   - generalization: an I-universal set for the given instance, in the sampling-amenable regime w_max > εw₀/n → one family, independent of the weights and of the law of M, universal for every weights uniform on I and every law of M, in every regime; reason: the guess φ̃ of guessing step 1 (the only place where weights, M and the regime enter) cancels in R̃_ℓ/Ẽ_ℓ, so the family enumerates the same grids normalized by φ; this also removes the log Δ
--   - generalization: "there exists … can be explicitly constructed" → the named program family, with its counted cost; reason: the program witnesses the existence
--   - reading: running time in an unspecified model → unit-cost real RAM: one unit per arithmetic operation, comparison, ⌊·⌋, ⌈·⌉, log, list access and loop dispatch; reason: the paper fixes no machine model
--   - encoding: O(·) → absolute constants c₁, c₂ chosen before n, C, I and ε; bounds on every run; reason: the usual reading of O(·) with universal constants
--   - encoding: n, C (the instance) → 1 ≤ n and 1 ≤ C; reason: the bound (nC)^{…} is 0 otherwise
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), Theorem 3, p.18; proof §4, pp.18–25

import Mathlib
import Definitions.Def_MNLStability_IsLaw
import Definitions.Def_MNLStability_IsUniversal
import Definitions.Def_MNLStability_IsPriceOrder
import Definitions.Def_MNLStability_family

namespace MNLStability

/-- **Theorem 3** (SSRN:3498325, p.18; proof §4, pp.18–25), for the explicit construction `family`.
There are absolute constants `c₁, c₂ > 0` such that for every `n ≥ 1`, every capacity `C ≥ 1`, every
non-negative prices, every set of products `I` listed by `ord` by non-increasing price, and every
`ε > 0`: the program `family r ord C ε` returns, on every run, a list `𝒰_I` of at most
`c₁·(nC)^{c₂/ε²}` vectors, after at most `c₁·(nC)^{c₂/ε²}` unit operations, and `𝒰_I` is
`I`-universal with accuracy `ε` for every positive weights that are uniform on `I` and every law of
the number of customers `M`. -/
theorem theorem_3 : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∀ (n C : ℕ), 1 ≤ n → 1 ≤ C → ∀ r : Fin n → ℝ, (∀ i, 0 ≤ r i) →
    ∀ (I : Finset (Fin n)) (ord : List (Fin n)), IsPriceOrder r I ord → ∀ ε : ℝ, 0 < ε →
    ∀ x ∈ ((family r ord C ε).run 0).support,
      (x.1.length : ℝ) ≤ c₁ * ((n * C : ℕ) : ℝ) ^ (c₂ / ε ^ 2) ∧
      (x.2 : ℝ) ≤ c₁ * ((n * C : ℕ) : ℝ) ^ (c₂ / ε ^ 2) ∧
      ∀ wts : Weights n, wts.Pos → wts.UniformOn I → ∀ pM : ℕ →₀ ℝ, IsLaw pM →
        IsUniversal wts r pM C ε I x.1 := by sorry

end MNLStability
