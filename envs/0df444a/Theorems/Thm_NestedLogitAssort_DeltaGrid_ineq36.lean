-- Prove2me | Theorems.Thm_NestedLogitAssort_DeltaGrid_ineq36
-- name    : NestedLogitAssort.DeltaGrid.ineq36
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:11:10.080513+00:00
-- url     : https://prove2.me/theorems/0a879ad7-6d51-4c07-a230-8d84e00bfbfc
-- title:
--   Inequality (36) in the proof of Theorem 12
-- statement:
--   Consider the nested logit model with a finite set $M$ of nests, each offering the products $N=\{1,\dots,n\}$ sorted so that $r_{i1}\ge\dots\ge r_{in}$; $v_{ij}$ is the preference weight and $r_{ij}$ the revenue of product $j$ in nest $i$, $v_{i0}$ the weight of the no-purchase option inside nest $i$, $v_0$ that of choosing no nest, and $\gamma_i\ge0$ the dissimilarity parameter of nest $i$. Write $V_i(S)=v_{i0}+\sum_{j\in S}v_{ij}$ and $R_i(S)=\sum_{j\in S}r_{ij}v_{ij}/V_i(S)$, with $R_i(\emptyset)=0$.
--
--   Assume the weights and revenues of nest $i$ are nonnegative, fix $\delta>1$, a real number $\bar\gamma$, a level $l\in\mathbb Z$, an assortment $S$ with $\delta^{l-1}\le V_i(S)\le\delta^l$, and an assortment $\hat S$ with the two properties of $\hat S_{il}$: $\delta^{l-1}\le V_i(\hat S)\le\delta^l$ and $\delta\sum_{j\in\hat S}r_{ij}v_{ij}\ge\hat G_{il}$ (the optimal value of (15)). If $x\ge0$ and $y_i\ge V_i(\hat S)^{\gamma_i}(R_i(\hat S)-x)$, then
--
--   $$
--   \begin{aligned}
--   \delta^{\bar\gamma+1}y_i&\ge\delta^{\bar\gamma}(\delta^l)^{\gamma_i-1}\delta^{-[\gamma_i-1]^+}\Bigl(\sum_{j\in S}r_{ij}v_{ij}\Bigr)-\delta^{\bar\gamma+1}(\delta^l)^{\gamma_i}x,\\
--   \delta^{\bar\gamma+1}y_i&\ge\delta^{\bar\gamma}(\delta^l)^{\gamma_i-1}\delta^{-[\gamma_i-1]^+}\Bigl(\sum_{j\in S}r_{ij}v_{ij}\Bigr)-\delta^{\bar\gamma+\gamma_i+1}(\delta^{l-1})^{\gamma_i}x .
--   \end{aligned}
--   $$
--
--   The two right-hand sides are equal; the second is the form the proof continues with. In the proof $(x,y_i)=(\hat x,\hat y_i)$, $\hat S=\hat S_{il}$ and $\bar\gamma=\max_i\gamma_i$.
--
--   Differences from the source:
--   - reading: r_ij is a revenue; its sign is not stated → hypothesis 0 ≤ r_ij; reason: revenues are nonnegative in the model; the proof uses it (x̂ ≥ 0 via p. 45: the right sides are positive when x̂ < 0; inserting (35) into (34) on p. 53 multiplies a lower bound by ∑ r v; Proposition 15's proof, p. 52, uses positive objective coefficients). With negative revenues the assortment Ŝ_il usually does not exist (if Ĝ_il < 0, no S satisfies δ∑rv ≥ Ĝ_il ≥ ∑rv); no counterexample to the theorem was found otherwise
--   - reading: v_i0, v_ij are preference weights (p. 7 allows v_i0 = 0 and padding products with v_ij = 0) → hypotheses 0 ≤ v_i0, 0 ≤ v_ij for the nest considered (zero allowed); reason: preference weights of a logit model are nonnegative; the remarks on p. 7 allow exactly the zero values
--   - generalization: (x̂, ŷ_i), the assortment Ŝ_il of Proposition 15, and γ̄ = max_i γ_i > 1 → any x ≥ 0 and y_i with y_i ≥ V_i(Ŝ)^γi(R_i(Ŝ) − x), any Ŝ with the two properties of Ŝ_il, any real γ̄, a single nest i; reason: x̂ ≥ 0 by xhat_nonneg, ŷ_i satisfies the constraint of (4) for Ŝ_il, and the step uses only these facts; the statement specializes to the page
--   - encoding: V_i(S_i)^γi and R_i(S_i) with the interpretation R_i(∅) = 0 → Real.rpow (0^0 = 1, 0^γ = 0 for γ ≠ 0) and division with a/0 = 0; reason: realizes R_i(∅) = 0; the 0^0 case (V_i(S) = 0 = γ_i) is not discussed by the paper and gets Lean's value 1
--   - encoding: δ ∑_{j∈Ŝ_il} r_ij v_ij ≥ Ĝ_il with Ĝ_il the maximum (15) → δ ∑_{j∈Ŝ} r_ij v_ij ≥ ∑_{j∈S} r_ij v_ij for every S in the window of level l; reason: Ĝ_il is the maximum of a finite set that is nonempty because Ŝ_il lies in the window, so the two are equivalent; avoids a real supremum
--   - encoding: δ^l, δ^(l−1) for l ∈ Z and the factors δ^(2γ̄+1), δ^(γ̄+1), δ^(−[a]^+) → zpow for the integer powers, Real.rpow for the real exponents, [a]^+ as max a 0; reason: Lean convention; same values
--   - encoding: products N = {1, …, n}, nests M = {1, …, m} → products Fin n (index 0 is product 1), nests a Fintype M; reason: Lean convention; same instances
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, proof of Theorem 12 (Appendix A.6), eqs. (34)–(36), p. 53

import Mathlib
import Definitions.Def_NestedLogitAssort_DeltaGrid_T
import Definitions.Def_NestedLogitAssort_DeltaGrid_IsApprox15

namespace NestedLogitAssort.DeltaGrid

/-- **Inequality (36).**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, proof of Theorem 12 (Appendix A.6), eqs. (34)–(36), p. 53: for an assortment `S_i` in the
window of level `l`,
`δ^{γ̄+1} ŷ_i ≥ δ^{γ̄} (δ^l)^{γ_i−1} δ^{−[γ_i−1]^+} (∑_{j∈S_i} r_{ij} v_{ij}) − δ^{γ̄+1} (δ^l)^{γ_i} x̂`
`= δ^{γ̄} (δ^l)^{γ_i−1} δ^{−[γ_i−1]^+} (∑_{j∈S_i} r_{ij} v_{ij}) − δ^{γ̄+γ_i+1} (δ^{l−1})^{γ_i} x̂`.

Stated for one nest `i`, any real `γ̄`, any `x ≥ 0` and any `y_i` with
`y_i ≥ V_i(Ŝ)^{γ_i}(R_i(Ŝ) − x)` for a `δ`-approximate solution `Ŝ` of (15) at level `l`; the page
has `(x, y_i) = (x̂, ŷ_i)`, `Ŝ = Ŝ_{il}` and `γ̄ = max_i γ_i`. Both right-hand sides of (36) are
stated.

**Formalization Note.** `δ ^ l` is `zpow`; the other powers are `Real.rpow`. -/
theorem ineq36 {M : Type*} {n : ℕ} (I : Instance M n) (i : M)
    (hw0 : 0 ≤ I.w0 i) (hv : ∀ j, 0 ≤ I.v i j) (hr : ∀ j, 0 ≤ I.r i j)
    (hγ0 : 0 ≤ I.γ i) (γbar : ℝ) (δ : ℝ) (hδ : 1 < δ) (x : ℝ) (hx : 0 ≤ x)
    (l : ℤ) (S Shat : Finset (Fin n)) (hS : Window I δ i l S) (hShat : IsApprox15 I δ i l Shat)
    (yi : ℝ) (hy : T I i Shat x ≤ yi) :
    δ ^ γbar * (δ ^ l) ^ (I.γ i - 1) * δ ^ (-(max (I.γ i - 1) 0)) *
          (∑ j ∈ S, I.r i j * I.v i j) - δ ^ (γbar + 1) * (δ ^ l) ^ (I.γ i) * x ≤
        δ ^ (γbar + 1) * yi ∧
      δ ^ γbar * (δ ^ l) ^ (I.γ i - 1) * δ ^ (-(max (I.γ i - 1) 0)) *
          (∑ j ∈ S, I.r i j * I.v i j) - δ ^ (γbar + I.γ i + 1) * (δ ^ (l - 1)) ^ (I.γ i) * x ≤
        δ ^ (γbar + 1) * yi := by sorry

end NestedLogitAssort.DeltaGrid
