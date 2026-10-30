-- Prove2me | Theorems.Thm_NestedLogitAssort_General_case2_integral
-- name    : NestedLogitAssort.General.case2_integral
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:52:03.235134+00:00
-- url     : https://prove2.me/theorems/7e491282-cd0a-4c36-86c2-b5fd4edb043c
-- title:
--   Proof of Theorem 11, Case 2: problem (31) is solved by a nested-by-revenue assortment
-- statement:
--   Consider the nested logit model with a finite set $M$ of nests, each offering the products $N=\{1,\dots,n\}$ sorted so that $r_{i1}\ge\dots\ge r_{in}$; $v_{ij}$ is the preference weight of product $j$ in nest $i$, $v_{i0}$ that of the no-purchase option inside nest $i$, $v_0$ that of choosing no nest, and $\gamma_i\ge0$ the dissimilarity parameter of nest $i$. Write $V_i(S)=v_{i0}+\sum_{j\in S}v_{ij}$ and $R_i(S)=\sum_{j\in S}r_{ij}v_{ij}/V_i(S)$, with $R_i(\emptyset)=0$.
--
--   Fix a nest $i$ with $\gamma_i>1$ and $v_{i0}>0$, nonnegative weights $v_{ij}$ and revenues $r_{ij}$, and numbers $x\ge0$, $y_i<0$, $b\ge1$. Then there is $k\in\{0,\dots,n\}$ such that the 0–1 vector of the nested-by-revenue assortment $N_{ik}=\{1,\dots,k\}$ maximizes the objective of problem (31),
--
--   $$
--   \sum_{j\in N}r_{ij}v_{ij}z_j-b\,x\Bigl(v_{i0}+\sum_{j\in N}v_{ij}z_j\Bigr)-b\,y_i\Bigl(v_{i0}+\sum_{j\in N}v_{ij}z_j\Bigr)^{1-\gamma_i},
--   $$
--
--   over all $z\in[0,1]^n$. In the proof, $b=\beta$, $x=\hat x$ and $y_i=\hat y_i$; the claim reduces Case 2 to the nested-by-revenue candidates.
--
--   Differences from the source:
--   - generalization: the step is stated for x = x̂, y_i = ŷ_i < 0 and b = β → arbitrary reals satisfying the constraints the step uses; reason: specializes to the page at (x̂, ŷ_i, β)
--   - reading: Case 2 (γ_i > 1, ŷ_i < 0) for nest i → hypothesis 0 < v_i0; reason: in Case 2 the nest is partially captured: for v_i0 = 0 the candidate ∅ gives ŷ_i ≥ 0; with v_i0 = 0 the supremum of (31) is +∞ (V^(1−γ) → ∞ as V → 0)
--   - reading: "{1, 2, …, k} for some k ∈ N" → k ∈ {0, …, n} (the empty assortment N_i0 allowed); reason: the prefix form with ẑ_i1 = ρ = 0 gives the empty assortment, which is the candidate N^n_i0 = ∅
--   - reading: r_ij is a revenue; its sign is not stated → hypothesis 0 ≤ r_ij; reason: revenues are nonnegative in the model; the proof of Theorem 11 uses it (p. 45 via p. 46 for x̂ ≥ 0, Case 2 on p. 48, Case 3 on p. 49). Without it Theorem 11 fails: v0 = 0, two nests with v_10 = v_20 = 0, γ = (0.7, 1.5), one product each, r = (−0.956, −0.343), v = (0.536, 0) give β = 2, x̂ = −0.956, ŷ = 0, and the constraint for {1} in nest 1 fails at (βx̂, βŷ)
--   - reading: v_ij are preference weights (p. 7 allows padding products with v_ij = 0) → hypothesis 0 ≤ v_ij (zero allowed); reason: preference weights of a logit model are nonnegative; the remarks on p. 7 allow exactly the zero values
--   - encoding: V_i(S_i)^γi and R_i(S_i) with the interpretation R_i(∅) = 0 → Real.rpow (0^0 = 1, 0^γ = 0 for γ ≠ 0) and division with a/0 = 0; reason: realizes R_i(∅) = 0; the 0^0 case (V_i(S) = 0 = γ_i) is not discussed by the paper and gets Lean's value 1
--   - encoding: products N = {1, …, n} with r_i1 ≥ … ≥ r_in → products Fin n (index 0 is product 1); the ordering is Antitone (r i); 1-based k and j are natural numbers; reason: Lean convention; same instances
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, proof of Theorem 11 (Appendix A.4), Case 2, p. 48

import Mathlib
import Definitions.Def_NestedLogitAssort_General_obj31
import Definitions.Def_NestedLogitAssort_General_indic
import Definitions.Def_NestedLogitAssort_General_NBR

namespace NestedLogitAssort.General

/-- **The claim in Case 2 of the proof of Theorem 11: problem (31) is solved by a nested-by-revenue assortment.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, proof of Theorem 11 (Appendix A.4), Case 2, p. 48 (unnumbered): "We claim that we have
either `ẑ_{ik} = 0` or `ẑ_{ik} = 1`, implying that the optimal solution to the problem above
corresponds to a nested-by-revenue assortment."

Let nest `i` have `γ_i > 1` and `v_{i0} > 0`, and let `x ≥ 0`, `y_i < 0` and `b ≥ 1`. Then the
maximum of the objective of (31) over `z_i ∈ [0, 1]^n` is attained at the 0–1 vector of a
nested-by-revenue assortment `N_{ik} = {1, …, k}` for some `k ∈ {0, …, n}`.

**Formalization Note.** On the page `b = β`, `x = x̂`, `y_i = ŷ_i`. `v_{i0} > 0` holds in this case of
the proof: for `v_{i0} = 0` the candidate `∅` gives `ŷ_i ≥ 0`. Hypotheses: `v_{ij} ≥ 0`, `r_{ij} ≥ 0`,
`r_{i1} ≥ … ≥ r_{in}` (`Antitone`, p. 7). `k = 0` (the empty assortment `N^n_{i0}`) is allowed. -/
theorem case2_integral {M : Type*} {n : ℕ} (I : Instance M n) (i : M)
    (hγ : 1 < I.γ i) (hw0 : 0 < I.w0 i) (hv : ∀ j, 0 ≤ I.v i j) (hr : ∀ j, 0 ≤ I.r i j)
    (hanti : Antitone (I.r i)) (x yi b : ℝ) (hx : 0 ≤ x) (hy : yi < 0) (hb : 1 ≤ b) :
    ∃ k : ℕ, k ≤ n ∧ ∀ z : Fin n → ℝ, (∀ j, 0 ≤ z j ∧ z j ≤ 1) →
      obj31 I i z x yi b ≤ obj31 I i (indic (NBR n k)) x yi b := by sorry

end NestedLogitAssort.General
