-- Prove2me | Theorems.Thm_LowAccLTC_Supplement_theorem_5_1_tensor_low_acceptance
-- name    : LowAccLTC.Supplement.theorem_5_1_tensor_low_acceptance
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:25:27.769995+00:00
-- url     : https://prove2.me/theorems/b50fb8cd-fad4-4c1a-bff4-ea096e86026e
-- title:
--   Theorem 5.1 — tensor codes are $(\varepsilon,x\mapsto x/4)$-low-acceptance locally testable
-- statement:
--   Let $F$ be a field, let $n\ge 1$, let $B \subseteq F^{[n]}$ be a linear code whose relative distance is at least $\delta \in [0,1]$, and let $0<\varepsilon<1/2$. Suppose
--
--   $$
--   r \ge \frac{10^{34}}{\varepsilon^{16}}
--     \log^2\!\left(\frac{5\cdot 10^5}{\varepsilon^2}\right)
--   \qquad\text{and}\qquad
--   \delta^r \ge 1-\frac{\varepsilon^2}{36}.
--   $$
--
--   Then $B^{\otimes r}$ is an $(\varepsilon,x\mapsto x/4)$-low-acceptance locally testable code under the uniform axis-parallel hyperplane test. Explicitly, for every word $f:[n]^r\to F$, if
--
--   $$
--   x:=1-\mathbb E_{i,a}\!\left[\operatorname{dist}\!\left(f|_{x_i=a},B^{\otimes(r-1)}\right)\right] \ge \varepsilon,
--   $$
--
--   then
--
--   $$
--   1-\operatorname{dist}(f,B^{\otimes r}) \ge \frac{x}{4}.
--   $$
--
--   Thus even when the average local agreement is only at least $\varepsilon$, it certifies global agreement at least one quarter as large.
--
--   **Formalization Note** $\log$ is the natural logarithm. The published `HasRelDistAtLeast` predicate gives the distance parameter lower-bound semantics, and directions and coordinates are represented by zero-based `Fin` types.
--
--   Differences from the source:
--
--   - generalization: C₀ is a linear code of distance δ → B has relative distance at least δ, with 0 ≤ δ ≤ 1; reason: the conclusion is monotone in the code's actual relative distance, and taking δ equal to the actual distance recovers every source instance
--   - encoding: a code has block length n and tensor order r in ℕ → n and r are natural numbers and the LA-LTC predicate records 0 < n and 0 < r; reason: the source's relative Hamming distance and uniform vertex test require nonempty coordinate and direction sets, and the displayed rank bound already forces r > 0
--   - encoding: ε < 1/2 in Theorem 5.1, under Definition 2.3 where ε ∈ (0,1) → separate hypotheses 0 < ε and ε < 1/2; reason: positivity is implicit in the source definition and is also required for the displayed reciprocal and logarithm
--   - encoding: log and the sets [n] and [r] → Real.log and zero-based types Fin n and Fin r; reason: the base mission's natural-log and finite-coordinate conventions, with the same uniform test and tensor code
--   - encoding: φ:[0,1]→ℝ+ is monotone nondecreasing and the LA-LTC implication holds → IsLALTCHyperplane represents φ on ℝ and bundles its nonnegativity and monotonicity on [0,1], the parameter ranges, and the implication; reason: this is the direct real-valued Lean encoding of Definition 2.3, and x↦x/4 satisfies the bundled conditions
-- source:
--   Ben Yaacov, Dikstein, Liu, Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs (manuscript, sha256 04242e17…), Theorem 5.1, p.43 (PDF p.46); Definition 2.3, p.14 (PDF p.17)

import Definitions.Def_LowAccLTC_Supplement_IsLALTCHyperplane

namespace LowAccLTC

namespace Supplement

/-- **Theorem 5.1** (Ben Yaacov–Dikstein–Liu,
*Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs*, unpublished
manuscript, sha256 04242e17…, p.43 = PDF p.46).

Let `0 < n`, `0 < ε < 1/2` and
`r ≥ 10^34 / ε^16 · log²(5·10^5 / ε²)`. If the linear code `B ⊆ F^[n]` has relative
distance at least `δ ∈ [0,1]` and `δ^r ≥ 1 - ε²/36`, then `B^{⊗r}` is an
`(ε, x ↦ x/4)`-low-acceptance locally testable code with respect to the vertex test, which in
this setting is the uniform axis-parallel hyperplane test.

**Formalization Note.** `log` is the natural logarithm. The paper's "distance `δ`" is used with
lower-bound semantics through `HasRelDistAtLeast`; the conclusion is monotone under increasing
the actual distance. Coordinates and tensor directions are zero-based `Fin` types. -/
theorem theorem_5_1_tensor_low_acceptance {F : Type*} [Field F] (n : ℕ) (hn : 0 < n)
    (B : Submodule F (Fin n → F)) (δ ε : ℝ) (hδ : 0 ≤ δ ∧ δ ≤ 1)
    (hB : HasRelDistAtLeast B δ) (hε0 : 0 < ε) (hε : ε < 1 / 2) (r : ℕ)
    (hr : (10 : ℝ) ^ 34 / ε ^ 16 * (Real.log (5 * (10 : ℝ) ^ 5 / ε ^ 2)) ^ 2 ≤ (r : ℝ))
    (hpow : 1 - ε ^ 2 / 36 ≤ δ ^ r) :
    IsLALTCHyperplane B r ε (fun x => x / 4) := by sorry

end Supplement

end LowAccLTC
