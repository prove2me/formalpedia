-- Prove2me | Theorems.Thm_NestedLogitAssort_General_case3_bound
-- name    : NestedLogitAssort.General.case3_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:20:11.427109+00:00
-- url     : https://prove2.me/theorems/ee9ce074-ce45-4e4c-892a-f8214462bd70
-- title:
--   Proof of Theorem 11, Case 3 ($\gamma_i\le1$): scaling from $2$ to $\beta$
-- statement:
--   Consider the nested logit model with a finite set $M$ of nests, each offering the products $N=\{1,\dots,n\}$ sorted so that $r_{i1}\ge\dots\ge r_{in}$; $v_{ij}$ is the preference weight of product $j$ in nest $i$, $v_{i0}$ that of the no-purchase option inside nest $i$, $v_0$ that of choosing no nest, and $\gamma_i\ge0$ the dissimilarity parameter of nest $i$. Write $V_i(S)=v_{i0}+\sum_{j\in S}v_{ij}$ and $R_i(S)=\sum_{j\in S}r_{ij}v_{ij}/V_i(S)$, with $R_i(\emptyset)=0$.
--
--   Fix a nest $i$ with $\gamma_i\le1$, $v_{i0}\ge0$, $v_{ij}\ge0$, $r_{ij}\ge0$, and let $b\ge2$. If
--
--   $$
--   2\,y_i\ \ge\ V_i(S)^{\gamma_i}\bigl(R_i(S)-2x\bigr)\qquad\text{for all }S\subseteq N,
--   $$
--
--   then
--
--   $$
--   b\,y_i\ \ge\ V_i(S)^{\gamma_i}\bigl(R_i(S)-b\,x\bigr)\qquad\text{for all }S\subseteq N .
--   $$
--
--   In the proof of Theorem 11, $b=\beta\ge2$, $x=\hat x$ and $y_i=\hat y_i$: the factor-two bound for nests with $\gamma_i\le1$ is lifted to the factor $\beta$ of (12).
--
--   Differences from the source:
--   - generalization: the step is stated for x = x̂, y_i = ŷ_i and b = β → arbitrary reals satisfying the constraints the step uses; reason: specializes to the page at (x̂, ŷ_i, β)
--   - reading: r_ij is a revenue; its sign is not stated → hypothesis 0 ≤ r_ij; reason: revenues are nonnegative in the model; the proof of Theorem 11 uses it (p. 45 via p. 46 for x̂ ≥ 0, Case 2 on p. 48, Case 3 on p. 49). Without it Theorem 11 fails: v0 = 0, two nests with v_10 = v_20 = 0, γ = (0.7, 1.5), one product each, r = (−0.956, −0.343), v = (0.536, 0) give β = 2, x̂ = −0.956, ŷ = 0, and the constraint for {1} in nest 1 fails at (βx̂, βŷ)
--   - reading: v_i0, v_ij are preference weights (p. 7 allows v_i0 = 0 and padding products with v_ij = 0) → hypotheses 0 ≤ v_i0, 0 ≤ v_ij (zero allowed); reason: preference weights of a logit model are nonnegative; the remarks on p. 7 allow exactly the zero values
--   - encoding: V_i(S_i)^γi and R_i(S_i) with the interpretation R_i(∅) = 0 → Real.rpow (0^0 = 1, 0^γ = 0 for γ ≠ 0) and division with a/0 = 0; reason: realizes R_i(∅) = 0; the 0^0 case (V_i(S) = 0 = γ_i) is not discussed by the paper and gets Lean's value 1
--   - generalization: γ_i ≥ 0 (p. 7) and products ordered so that r_i1 ≥ … ≥ r_in (p. 7) → neither assumed (only γ_i ≤ 1); reason: the scaling step uses only R_i(S) ≥ 0 and V_i(S)^γi ≥ 0; it specializes to the page
--   - encoding: products N = {1, …, n} → products Fin n (index 0 is product 1); 1-based k and j are natural numbers; reason: Lean convention; same instances
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, proof of Theorem 11 (Appendix A.4), Case 3, pp. 48–49

import Mathlib
import Definitions.Def_NestedLogitAssort_General_T

namespace NestedLogitAssort.General

/-- **Case 3 of the proof of Theorem 11: `γ_i ≤ 1`, scaling from `2` to `β`.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, proof of Theorem 11 (Appendix A.4), Case 3, pp. 48–49 (unnumbered): "Multiplying this
inequality by `β/2 ≥ 1`, we obtain `β ŷ_i ≥ V_i(S_i)^{γ_i}(β R_i(S_i)/2 − β x̂) ≥ V_i(S_i)^{γ_i}(R_i(S_i) − β x̂)`
for all `S_i ⊂ N`."

For a nest with `γ_i ≤ 1` and `b ≥ 2`, if `2 y_i ≥ V_i(S)^{γ_i}(R_i(S) − 2x)` for every `S ⊂ N`, then
`b y_i ≥ V_i(S)^{γ_i}(R_i(S) − b x)` for every `S ⊂ N`.

**Formalization Note.** On the page `b = β`, `x = x̂`, `y_i = ŷ_i`. Hypotheses: `v_{i0}, v_{ij} ≥ 0`,
`r_{ij} ≥ 0` (so that `R_i(S) ≥ 0`). -/
theorem case3_bound {M : Type*} {n : ℕ} (I : Instance M n) (i : M)
    (hγ1 : I.γ i ≤ 1) (hw0 : 0 ≤ I.w0 i) (hv : ∀ j, 0 ≤ I.v i j) (hr : ∀ j, 0 ≤ I.r i j)
    (x yi b : ℝ) (hb : 2 ≤ b) (h2 : ∀ S : Finset (Fin n), T I i S (2 * x) ≤ 2 * yi) :
    ∀ S : Finset (Fin n), T I i S (b * x) ≤ b * yi := by sorry

end NestedLogitAssort.General
