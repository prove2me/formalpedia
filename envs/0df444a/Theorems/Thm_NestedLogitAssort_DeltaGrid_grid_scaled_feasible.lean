-- Prove2me | Theorems.Thm_NestedLogitAssort_DeltaGrid_grid_scaled_feasible
-- name    : NestedLogitAssort.DeltaGrid.grid_scaled_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:14:22.690311+00:00
-- url     : https://prove2.me/theorems/e2598426-5a96-4fce-9e35-2a17c8e81ac0
-- title:
--   Theorem 12 — the grid collection $\{\hat S_{il}\}\cup\{\emptyset\}$ gives a solution of (3) after scaling by $\delta^{2\bar\gamma+1}$ and $\delta^{\bar\gamma+1}$
-- statement:
--   Consider the nested logit model with a finite set $M$ of nests, each offering the products $N=\{1,\dots,n\}$ sorted so that $r_{i1}\ge\dots\ge r_{in}$; $v_{ij}$ is the preference weight and $r_{ij}$ the revenue of product $j$ in nest $i$, $v_{i0}$ the weight of the no-purchase option inside nest $i$, $v_0$ that of choosing no nest, and $\gamma_i\ge0$ the dissimilarity parameter of nest $i$. Write $V_i(S)=v_{i0}+\sum_{j\in S}v_{ij}$ and $R_i(S)=\sum_{j\in S}r_{ij}v_{ij}/V_i(S)$, with $R_i(\emptyset)=0$.
--
--   Assume all weights and revenues are nonnegative, let $\bar\gamma=\max_{i\in M}\gamma_i$ and assume $\bar\gamma>1$ (the standing assumption of Section 6), and fix $\delta>1$. For every nest $i$ let $v^L_i=v_{i0}+\min_{j\in N}v_{ij}$, $v^U_i=v_{i0}+\sum_{j\in N}v_{ij}$, $l^L_i=\min\{l\in\mathbb Z:\delta^l\ge v^L_i\}$ and $l^U_i=\min\{l\in\mathbb Z:\delta^l\ge v^U_i\}$. For every level $l=l^L_i,\dots,l^U_i$ at which problem
--
--   $$
--   \hat G_{il}=\max_{S_i\subseteq N}\Bigl\{\sum_{j\in S_i}r_{ij}v_{ij}:\ \delta^{l-1}\le v_{i0}+\sum_{j\in S_i}v_{ij}\le\delta^l\Bigr\}\tag{15}
--   $$
--
--   is feasible, let $\hat S_{il}$ be an assortment with $\delta^{l-1}\le v_{i0}+\sum_{j\in\hat S_{il}}v_{ij}\le\delta^l$ and $\delta\sum_{j\in\hat S_{il}}r_{ij}v_{ij}\ge\hat G_{il}$.
--
--   Let $(\hat x,\hat y)$ be an optimal solution of the linear program (4) in which the candidate collection of nest $i$ is $\{\hat S_{il}:l=l^L_i,\dots,l^U_i\}\cup\{\emptyset\}$. Then
--
--   $$
--   \bigl(\delta^{2\bar\gamma+1}\hat x,\ \delta^{\bar\gamma+1}\hat y\bigr)\ \text{is a feasible solution of the linear program (3).}
--   $$
--
--   Combined with Theorem 1 of the paper, this gives an assortment whose expected revenue is within a factor $\delta^{2\bar\gamma+1}$ of the optimum, from a linear program with $1+m$ variables and $O(m\log_\delta(v^U_i/v^L_i))$ constraints; letting $\delta\downarrow1$ trades computation for accuracy.
--
--   **Formalization Note** $\bar\gamma$ is a variable with `IsGreatest (Set.range γ) γbar`, which is exactly $\bar\gamma=\max_i\gamma_i$ and forces $M\ne\emptyset$. The assortments $\hat S_{il}$ are an arbitrary selection with the two properties above (`IsApprox15`).
--
--   Differences from the source:
--   - reading: r_ij is a revenue; its sign is not stated → hypothesis 0 ≤ r_ij; reason: revenues are nonnegative in the model; the proof uses it (x̂ ≥ 0 via p. 45: the right sides are positive when x̂ < 0; inserting (35) into (34) on p. 53 multiplies a lower bound by ∑ r v; Proposition 15's proof, p. 52, uses positive objective coefficients). With negative revenues the assortment Ŝ_il usually does not exist (if Ĝ_il < 0, no S satisfies δ∑rv ≥ Ĝ_il ≥ ∑rv); no counterexample to the theorem was found otherwise
--   - reading: v0, v_i0, v_ij are preference weights (p. 7 allows v_i0 = 0, padding products with v_ij = 0, and v0 = 0) → hypotheses 0 ≤ v0, 0 ≤ v_i0, 0 ≤ v_ij (zero allowed); reason: preference weights of a logit model are nonnegative; the remarks on p. 7 allow exactly the zero values
--   - reading: levels l = l^L_i, …, l^U_i with l^L_i = min{l ∈ Z : δ^l ≥ v^L_i}, l^U_i = min{l ∈ Z : δ^l ≥ v^U_i} → InLevelRange: (∃ j, v_i0 + v_ij ≤ δ^l) ∧ δ^(l−1) < v^U_i, the defining inequalities of the two minima; reason: equal to l^L_i ≤ l ≤ l^U_i whenever v^L_i > 0; when v^L_i = 0 (v_i0 = 0 and a zero-weight product, allowed on p. 7) the printed minimum l^L_i does not exist and every l ≤ l^U_i is admitted, and only finitely many of these levels have (15) feasible; when v^U_i = 0 or n = 0 no level is in range
--   - reading: the collection {Ŝ_il : l = l^L_i, …, l^U_i} ∪ {∅}, with Ŝ_il produced by Proposition 15, which assumes that (15) (= (32)) has a feasible solution → CandGrid contains Shat i l only at in-range levels where (15) is feasible (Feasible15), and the properties of Shat i l are required only there; reason: at a level whose window contains no assortment there is no Ŝ_il with δ^(l−1) ≤ V_i(Ŝ_il) ≤ δ^l, so the paper's collection cannot contain one
--   - generalization: Ŝ_il is the assortment found by Proposition 15, with δ^(l−1) ≤ V_i(Ŝ_il) ≤ δ^l and δ ∑_{j∈Ŝ_il} r_ij v_ij ≥ Ĝ_il → Shat : M → ℤ → Finset (Fin n) is any choice with these two properties (IsApprox15) at every in-range feasible level; reason: the page defines Ŝ_il by these two properties and the proof (A.6) uses only them; Proposition 15's output is one such choice, so the statement specializes to the page
--   - encoding: V_i(S_i)^γi and R_i(S_i) with the interpretation R_i(∅) = 0 → Real.rpow (0^0 = 1, 0^γ = 0 for γ ≠ 0) and division with a/0 = 0; reason: realizes R_i(∅) = 0; the 0^0 case (V_i(S) = 0 = γ_i) is not discussed by the paper and gets Lean's value 1
--   - encoding: problems (3) and (4) are min-x linear programs with variables x and (y_i)_{i∈M} → Feas3 (feasibility in (3)) and IsOpt4 (feasible for (4) and no feasible point has smaller x), y : M → ℝ; reason: only feasibility in (3) and optimality in (4) enter the statement
--   - encoding: δ ∑_{j∈Ŝ_il} r_ij v_ij ≥ Ĝ_il with Ĝ_il the maximum (15) → δ ∑_{j∈Ŝ} r_ij v_ij ≥ ∑_{j∈S} r_ij v_ij for every S in the window of level l; reason: Ĝ_il is the maximum of a finite set that is nonempty because Ŝ_il lies in the window, so the two are equivalent; avoids a real supremum
--   - encoding: δ^l, δ^(l−1) for l ∈ Z and the factors δ^(2γ̄+1), δ^(γ̄+1), δ^(−[a]^+) → zpow for the integer powers, Real.rpow for the real exponents, [a]^+ as max a 0; reason: Lean convention; same values
--   - encoding: products N = {1, …, n}, nests M = {1, …, m} → products Fin n (index 0 is product 1), nests a Fintype M; reason: Lean convention; same instances
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, Theorem 12, p. 28; Section 6, p. 25; Section 6.2, pp. 27–28; proof in Appendix A.6, pp. 53–54

import Mathlib
import Definitions.Def_NestedLogitAssort_DeltaGrid_Feas3
import Definitions.Def_NestedLogitAssort_DeltaGrid_IsOpt4
import Definitions.Def_NestedLogitAssort_DeltaGrid_IsApprox15
import Definitions.Def_NestedLogitAssort_DeltaGrid_CandGrid

namespace NestedLogitAssort.DeltaGrid

/-- **Theorem 12: the grid collection gives a solution of (3) after scaling by `δ^{2γ̄+1}` and `δ^{γ̄+1}`.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, Theorem 12, p. 28: "Let `(x̂, ŷ)` be an optimal solution to problem (4) when we solve this
problem after replacing the collection of candidate assortments `{A_{it} : t ∈ T_i}` in the second
set of constraints with the assortments `{Ŝ_{il} : l = l^L_i, …, l^U_i} ∪ {∅}`. Then,
`(δ^{2γ̄+1} x̂, δ^{γ̄+1} ŷ)` is a feasible solution to problem (3)."

Setting: the nested logit model of Section 1 (p. 7) with nonnegative weights and revenues,
`r_{i1} ≥ … ≥ r_{in}`, `γ_i ≥ 0`; Section 6 (p. 25): `γ̄ = max_{i∈M} γ_i` and `γ̄ > 1`;
Section 6.2 (pp. 27–28): `δ > 1`, the levels `l = l^L_i, …, l^U_i`, and for each such level an
assortment `Ŝ_{il}` with `δ^{l−1} ≤ V_i(Ŝ_{il}) ≤ δ^l` and `δ ∑_{j∈Ŝ_{il}} r_{ij}v_{ij} ≥ Ĝ_{il}` (15).

**Formalization Note.**
* `γ̄` is a variable with `IsGreatest (Set.range I.γ) γbar`, i.e. `γ̄ = max_i γ_i` (this also makes
  `M` nonempty).
* `Shat i l` is any choice of assortments with the two properties of `Ŝ_{il}` (`IsApprox15`) at
  every in-range level where (15) is feasible; Proposition 15's construction is one such choice.
  The collection is `CandGrid` (`∅` and these assortments).
* The level range is `InLevelRange` (the defining inequalities of `l^L_i` and `l^U_i`).
* `δ ^ l` is `zpow`; `δ ^ (2 * γbar + 1)`, `δ ^ (γbar + 1)` and `V^γ` are `Real.rpow`. -/
theorem grid_scaled_feasible {M : Type*} [Fintype M] {n : ℕ} (I : Instance M n)
    (hv0 : 0 ≤ I.v0) (hw0 : ∀ i, 0 ≤ I.w0 i) (hv : ∀ i j, 0 ≤ I.v i j)
    (hr : ∀ i j, 0 ≤ I.r i j) (hanti : ∀ i, Antitone (I.r i))
    (hγ0 : ∀ i, 0 ≤ I.γ i)
    (γbar : ℝ) (hγbar : IsGreatest (Set.range I.γ) γbar) (hγbar1 : 1 < γbar)
    (δ : ℝ) (hδ : 1 < δ)
    (Shat : M → ℤ → Finset (Fin n))
    (hShat : ∀ i l, InLevelRange I δ i l → Feasible15 I δ i l → IsApprox15 I δ i l (Shat i l))
    (x : ℝ) (y : M → ℝ) (hopt : IsOpt4 I (fun i => CandGrid I δ Shat i) x y) :
    Feas3 I (δ ^ (2 * γbar + 1) * x) (fun i => δ ^ (γbar + 1) * y i) := by sorry

end NestedLogitAssort.DeltaGrid
