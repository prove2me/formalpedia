-- Prove2me | Theorems.Thm_NestedLogitAssort_DeltaGrid_constraint_zero_weight
-- name    : NestedLogitAssort.DeltaGrid.constraint_zero_weight
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:13:00.865159+00:00
-- url     : https://prove2.me/theorems/1372fae4-fc87-494a-aa77-b9370f79a019
-- title:
--   Proof of Theorem 12: the scaled solution satisfies the constraint of (3) for $S_i=\emptyset$
-- statement:
--   Consider the nested logit model with a finite set $M$ of nests, each offering the products $N=\{1,\dots,n\}$ sorted so that $r_{i1}\ge\dots\ge r_{in}$; $v_{ij}$ is the preference weight and $r_{ij}$ the revenue of product $j$ in nest $i$, $v_{i0}$ the weight of the no-purchase option inside nest $i$, $v_0$ that of choosing no nest, and $\gamma_i\ge0$ the dissimilarity parameter of nest $i$. Write $V_i(S)=v_{i0}+\sum_{j\in S}v_{ij}$ and $R_i(S)=\sum_{j\in S}r_{ij}v_{ij}/V_i(S)$, with $R_i(\emptyset)=0$.
--
--   Fix $\delta>1$, $\bar\gamma\ge0$ and a nest $i$ with nonnegative weights. Let $x\ge0$ and let $y_i$ satisfy the constraint of (4) for the empty assortment, $y_i\ge V_i(\emptyset)^{\gamma_i}(R_i(\emptyset)-x)$. Then every assortment $S$ that is empty, or has total weight $V_i(S)=0$, satisfies
--
--   $$
--   \delta^{\bar\gamma+1}y_i\ge V_i(S)^{\gamma_i}\bigl(R_i(S)-\delta^{2\bar\gamma+1}x\bigr).
--   $$
--
--   For $S=\emptyset$ this is the second case of the proof of Theorem 12. A nonempty $S$ with $V_i(S)=0$ occurs only when $v_{i0}=0$ and all products of $S$ have weight $0$; then $V_i(S)=V_i(\emptyset)$ and $R_i(S)=R_i(\emptyset)=0$.
--
--   Differences from the source:
--   - reading: v_i0, v_ij are preference weights (p. 7 allows v_i0 = 0 and padding products with v_ij = 0) → hypotheses 0 ≤ v_i0, 0 ≤ v_ij for the nest considered (zero allowed); reason: preference weights of a logit model are nonnegative; the remarks on p. 7 allow exactly the zero values
--   - generalization: the case S_i = ∅, for (x̂, ŷ_i) and γ̄ = max_i γ_i > 1 → every S with S = ∅ or V_i(S) = 0, any x ≥ 0 and y_i satisfying the ∅ constraint of (4), any γ̄ ≥ 0, a single nest i; reason: the zero-weight nonempty assortments are not treated on the page (where they exist the printed l^L_i is undefined) and have the same constraint value as ∅; S = ∅ with (x̂, ŷ_i) and γ̄ > 1 is the page's case
--   - encoding: V_i(S_i)^γi and R_i(S_i) with the interpretation R_i(∅) = 0 → Real.rpow (0^0 = 1, 0^γ = 0 for γ ≠ 0) and division with a/0 = 0; reason: realizes R_i(∅) = 0; the 0^0 case (V_i(S) = 0 = γ_i) is not discussed by the paper and gets Lean's value 1
--   - encoding: δ^l, δ^(l−1) for l ∈ Z and the factors δ^(2γ̄+1), δ^(γ̄+1), δ^(−[a]^+) → zpow for the integer powers, Real.rpow for the real exponents, [a]^+ as max a 0; reason: Lean convention; same values
--   - encoding: products N = {1, …, n}, nests M = {1, …, m} → products Fin n (index 0 is product 1), nests a Fintype M; reason: Lean convention; same instances
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, proof of Theorem 12 (Appendix A.6), case S_i = ∅, p. 54

import Mathlib
import Definitions.Def_NestedLogitAssort_DeltaGrid_T

namespace NestedLogitAssort.DeltaGrid

/-- **The scaled solution satisfies the constraint of (3) for `S_i = ∅` (and for zero-weight assortments).**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, proof of Theorem 12 (Appendix A.6), case `S_i = ∅`, p. 54 (unnumbered): from
`ŷ_i ≥ V_i(∅)^{γ_i}(R_i(∅) − x̂)`, multiplying by `δ^{γ̄+1}`, using `R_i(∅) = 0` and replacing
`δ^{γ̄+1}` by the larger `δ^{2γ̄+1}`, "`δ^{γ̄+1} ŷ_i ≥ V_i(∅)^{γ_i} R_i(∅) − δ^{2γ̄+1} V_i(∅)^{γ_i} x̂`".

For one nest `i` with nonnegative weights, `γ̄ ≥ 0`, `δ > 1`, `x ≥ 0` and any `y_i` with
`y_i ≥ V_i(∅)^{γ_i}(R_i(∅) − x)`: every assortment `S` that is empty or has `V_i(S) = 0` satisfies
`δ^{γ̄+1} y_i ≥ V_i(S)^{γ_i}(R_i(S) − δ^{2γ̄+1} x)`.

**Formalization Note.** The page has `(x, y_i) = (x̂, ŷ_i)` and `γ̄ = max_i γ_i > 1`. The case
`V_i(S) = 0`, `S ≠ ∅` (possible only when `v_{i0} = 0` and the products of `S` have weight `0`)
is not treated on the page; there `V_i(S) = V_i(∅) = 0` and `R_i(S) = R_i(∅) = 0`. -/
theorem constraint_zero_weight {M : Type*} {n : ℕ} (I : Instance M n) (i : M)
    (hw0 : 0 ≤ I.w0 i) (hv : ∀ j, 0 ≤ I.v i j) (γbar : ℝ) (hγbar0 : 0 ≤ γbar)
    (δ : ℝ) (hδ : 1 < δ) (x : ℝ) (hx : 0 ≤ x) (yi : ℝ) (hy : T I i ∅ x ≤ yi)
    (S : Finset (Fin n)) (hS : S = ∅ ∨ V I i S = 0) :
    T I i S (δ ^ (2 * γbar + 1) * x) ≤ δ ^ (γbar + 1) * yi := by sorry

end NestedLogitAssort.DeltaGrid
