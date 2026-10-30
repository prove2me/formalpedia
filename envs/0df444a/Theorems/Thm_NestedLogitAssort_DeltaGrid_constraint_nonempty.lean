-- Prove2me | Theorems.Thm_NestedLogitAssort_DeltaGrid_constraint_nonempty
-- name    : NestedLogitAssort.DeltaGrid.constraint_nonempty
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:12:35.136982+00:00
-- url     : https://prove2.me/theorems/cd75edf8-13fa-487c-9f75-c551c12339c2
-- title:
--   Proof of Theorem 12: the scaled solution satisfies the constraints of (3) for nonempty assortments
-- statement:
--   Consider the nested logit model with a finite set $M$ of nests, each offering the products $N=\{1,\dots,n\}$ sorted so that $r_{i1}\ge\dots\ge r_{in}$; $v_{ij}$ is the preference weight and $r_{ij}$ the revenue of product $j$ in nest $i$, $v_{i0}$ the weight of the no-purchase option inside nest $i$, $v_0$ that of choosing no nest, and $\gamma_i\ge0$ the dissimilarity parameter of nest $i$. Write $V_i(S)=v_{i0}+\sum_{j\in S}v_{ij}$ and $R_i(S)=\sum_{j\in S}r_{ij}v_{ij}/V_i(S)$, with $R_i(\emptyset)=0$.
--
--   Fix $\delta>1$ and $\bar\gamma>1$, and a nest $i$ with nonnegative weights and revenues and $0\le\gamma_i\le\bar\gamma$. For every level $l$ with $l^L_i\le l\le l^U_i$ at which problem (15) is feasible, let $\hat S_{il}$ be an assortment with $\delta^{l-1}\le V_i(\hat S_{il})\le\delta^l$ and $\delta\sum_{j\in\hat S_{il}}r_{ij}v_{ij}\ge\hat G_{il}$. Let $x\ge0$ and let $y_i$ satisfy $y_i\ge V_i(\hat S_{il})^{\gamma_i}(R_i(\hat S_{il})-x)$ at all these levels. Then every nonempty assortment $S\subseteq N$ with $V_i(S)>0$ satisfies
--
--   $$
--   \delta^{\bar\gamma+1}y_i\ge V_i(S)^{\gamma_i}\bigl(R_i(S)-\delta^{2\bar\gamma+1}x\bigr),
--   $$
--
--   which is the constraint of (3) for nest $i$ and assortment $S$ at the scaled point $(\delta^{2\bar\gamma+1}x,\delta^{\bar\gamma+1}y)$. In the proof of Theorem 12, $(x,y_i)=(\hat x,\hat y_i)$ and $\bar\gamma=\max_i\gamma_i$.
--
--   Differences from the source:
--   - reading: r_ij is a revenue; its sign is not stated → hypothesis 0 ≤ r_ij; reason: revenues are nonnegative in the model; the proof uses it (x̂ ≥ 0 via p. 45: the right sides are positive when x̂ < 0; inserting (35) into (34) on p. 53 multiplies a lower bound by ∑ r v; Proposition 15's proof, p. 52, uses positive objective coefficients). With negative revenues the assortment Ŝ_il usually does not exist (if Ĝ_il < 0, no S satisfies δ∑rv ≥ Ĝ_il ≥ ∑rv); no counterexample to the theorem was found otherwise
--   - reading: v_i0, v_ij are preference weights (p. 7 allows v_i0 = 0 and padding products with v_ij = 0) → hypotheses 0 ≤ v_i0, 0 ≤ v_ij for the nest considered (zero allowed); reason: preference weights of a logit model are nonnegative; the remarks on p. 7 allow exactly the zero values
--   - reading: levels l = l^L_i, …, l^U_i with l^L_i = min{l ∈ Z : δ^l ≥ v^L_i}, l^U_i = min{l ∈ Z : δ^l ≥ v^U_i} → InLevelRange: (∃ j, v_i0 + v_ij ≤ δ^l) ∧ δ^(l−1) < v^U_i, the defining inequalities of the two minima; reason: equal to l^L_i ≤ l ≤ l^U_i whenever v^L_i > 0; when v^L_i = 0 (v_i0 = 0 and a zero-weight product, allowed on p. 7) the printed minimum l^L_i does not exist and every l ≤ l^U_i is admitted, and only finitely many of these levels have (15) feasible; when v^U_i = 0 or n = 0 no level is in range
--   - reading: the collection {Ŝ_il : l = l^L_i, …, l^U_i} ∪ {∅}, with Ŝ_il produced by Proposition 15, which assumes that (15) (= (32)) has a feasible solution → CandGrid contains Shat i l only at in-range levels where (15) is feasible (Feasible15), and the properties of Shat i l are required only there; reason: at a level whose window contains no assortment there is no Ŝ_il with δ^(l−1) ≤ V_i(Ŝ_il) ≤ δ^l, so the paper's collection cannot contain one
--   - reading: case S_i ≠ ∅: fix l = l^L_i, …, l^U_i with δ^(l−1) ≤ V_i(S_i) ≤ δ^l → hypotheses S nonempty and 0 < V_i(S); reason: for S_i ≠ ∅ the page uses v^L_i ≤ V_i(S_i), so V_i(S_i) > 0 whenever v^L_i > 0, i.e. whenever l^L_i is defined; a nonempty S with V_i(S) = 0 (v_i0 = 0 and zero-weight products, e.g. one product with v_i1 = 0) lies in no window since δ^(l−1) > 0, and that case is covered by constraint_zero_weight through T(S, ·) = T(∅, ·)
--   - generalization: Ŝ_il is the assortment found by Proposition 15, with δ^(l−1) ≤ V_i(Ŝ_il) ≤ δ^l and δ ∑_{j∈Ŝ_il} r_ij v_ij ≥ Ĝ_il → Shat : M → ℤ → Finset (Fin n) is any choice with these two properties (IsApprox15) at every in-range feasible level; reason: the page defines Ŝ_il by these two properties and the proof (A.6) uses only them; Proposition 15's output is one such choice, so the statement specializes to the page
--   - generalization: (x̂, ŷ_i), the optimal solution of (4), and γ̄ = max_i γ_i → any x ≥ 0 and y_i satisfying the constraints of (4) for the Ŝ_il of nest i, any γ̄ with γ_i ≤ γ̄ and γ̄ > 1, a single nest i; reason: x̂ ≥ 0 by xhat_nonneg, ŷ_i satisfies these constraints, and γ_i ≤ max_i γ_i; the statement specializes to the page
--   - encoding: V_i(S_i)^γi and R_i(S_i) with the interpretation R_i(∅) = 0 → Real.rpow (0^0 = 1, 0^γ = 0 for γ ≠ 0) and division with a/0 = 0; reason: realizes R_i(∅) = 0; the 0^0 case (V_i(S) = 0 = γ_i) is not discussed by the paper and gets Lean's value 1
--   - encoding: δ ∑_{j∈Ŝ_il} r_ij v_ij ≥ Ĝ_il with Ĝ_il the maximum (15) → δ ∑_{j∈Ŝ} r_ij v_ij ≥ ∑_{j∈S} r_ij v_ij for every S in the window of level l; reason: Ĝ_il is the maximum of a finite set that is nonempty because Ŝ_il lies in the window, so the two are equivalent; avoids a real supremum
--   - encoding: δ^l, δ^(l−1) for l ∈ Z and the factors δ^(2γ̄+1), δ^(γ̄+1), δ^(−[a]^+) → zpow for the integer powers, Real.rpow for the real exponents, [a]^+ as max a 0; reason: Lean convention; same values
--   - encoding: products N = {1, …, n}, nests M = {1, …, m} → products Fin n (index 0 is product 1), nests a Fintype M; reason: Lean convention; same instances
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, proof of Theorem 12 (Appendix A.6), case S_i ≠ ∅, pp. 53–54

import Mathlib
import Definitions.Def_NestedLogitAssort_DeltaGrid_T
import Definitions.Def_NestedLogitAssort_DeltaGrid_IsApprox15
import Definitions.Def_NestedLogitAssort_DeltaGrid_InLevelRange
import Definitions.Def_NestedLogitAssort_DeltaGrid_Feasible15

namespace NestedLogitAssort.DeltaGrid

/-- **The scaled solution satisfies the constraint of (3) for every nonempty assortment.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, proof of Theorem 12 (Appendix A.6), p. 54 (unnumbered): "`δ^{γ̄+1} ŷ_i ≥
V_i(S_i)^{γ_i−1} (∑_{j∈S_i} r_{ij} v_{ij}) − δ^{2γ̄+1} V_i(S_i)^{γ_i} x̂`. Since
`∑_{j∈S_i} r_{ij}v_{ij}/V_i(S_i) = R_i(S_i)`, the inequality above shows that the solution
`(δ^{2γ̄+1} x̂, δ^{γ̄+1} ŷ)` satisfies the second set of constraints in problem (3) for the
assortment `S_i` and nest `i`, as long as `S_i ≠ ∅`."

For one nest `i` with nonnegative weights and revenues, `0 ≤ γ_i ≤ γ̄`, `γ̄ > 1`, `δ > 1`,
`x ≥ 0`, a choice `Ŝ_{il}` of `δ`-approximate solutions of (15) at every in-range level where (15)
is feasible, and any `y_i` with `y_i ≥ V_i(Ŝ_{il})^{γ_i}(R_i(Ŝ_{il}) − x)` at those levels: every
nonempty `S` with `V_i(S) > 0` satisfies
`δ^{γ̄+1} y_i ≥ V_i(S)^{γ_i}(R_i(S) − δ^{2γ̄+1} x)`.

**Formalization Note.** The page has `(x, y_i) = (x̂, ŷ_i)` and `γ̄ = max_i γ_i`. Nonempty
assortments with `V_i(S) = 0` are covered by `constraint_zero_weight`. -/
theorem constraint_nonempty {M : Type*} {n : ℕ} (I : Instance M n) (i : M)
    (hw0 : 0 ≤ I.w0 i) (hv : ∀ j, 0 ≤ I.v i j) (hr : ∀ j, 0 ≤ I.r i j)
    (γbar : ℝ) (hγ0 : 0 ≤ I.γ i) (hγle : I.γ i ≤ γbar) (hγbar1 : 1 < γbar)
    (δ : ℝ) (hδ : 1 < δ) (x : ℝ) (hx : 0 ≤ x) (Shat : ℤ → Finset (Fin n))
    (hShat : ∀ l, InLevelRange I δ i l → Feasible15 I δ i l → IsApprox15 I δ i l (Shat l))
    (yi : ℝ) (hy : ∀ l, InLevelRange I δ i l → Feasible15 I δ i l → T I i (Shat l) x ≤ yi)
    (S : Finset (Fin n)) (hS : S.Nonempty) (hpos : 0 < V I i S) :
    T I i S (δ ^ (2 * γbar + 1) * x) ≤ δ ^ (γbar + 1) * yi := by sorry

end NestedLogitAssort.DeltaGrid
