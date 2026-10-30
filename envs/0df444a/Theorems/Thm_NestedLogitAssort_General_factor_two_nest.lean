-- Prove2me | Theorems.Thm_NestedLogitAssort_General_factor_two_nest
-- name    : NestedLogitAssort.General.factor_two_nest
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:55:07.042364+00:00
-- url     : https://prove2.me/theorems/68702d80-e60d-4589-beae-3fc380a3fb1b
-- title:
--   Proof of Theorem 10, eqs. (26)–(29): the factor-two bound for one nest
-- statement:
--   Consider the nested logit model with a finite set $M$ of nests, each offering the products $N=\{1,\dots,n\}$ sorted so that $r_{i1}\ge\dots\ge r_{in}$; $v_{ij}$ is the preference weight of product $j$ in nest $i$, $v_{i0}$ that of the no-purchase option inside nest $i$, $v_0$ that of choosing no nest, and $\gamma_i\ge0$ the dissimilarity parameter of nest $i$. Write $V_i(S)=v_{i0}+\sum_{j\in S}v_{ij}$ and $R_i(S)=\sum_{j\in S}r_{ij}v_{ij}/V_i(S)$, with $R_i(\emptyset)=0$.
--
--   Fix a nest $i$ with $0\le\gamma_i\le1$, $v_{i0}\ge0$, $v_{ij}\ge0$, $r_{ij}\ge0$, and let $x\ge0$. Let $\hat S_i(\epsilon)$ be the greedy assortment of the continuous knapsack (11). Suppose $y_i$ satisfies
--
--   1. $y_i\ge V_i(\hat S_i(\epsilon))^{\gamma_i}\bigl(R_i(\hat S_i(\epsilon))-x\bigr)$ for every $\epsilon\ge0$;
--   2. $y_i\ge V_i(N)^{\gamma_i}\bigl(R_i(N)-x\bigr)$ (the case $\epsilon=\infty$);
--   3. $y_i\ge V_i(\{j\})^{\gamma_i}\bigl(R_i(\{j\})-x\bigr)$ for every $j\in N$.
--
--   Then
--
--   $$
--   2\,y_i\ \ge\ V_i(S)^{\gamma_i}\bigl(R_i(S)-2x\bigr)\qquad\text{for all }S\subseteq N .
--   $$
--
--   This is the per-nest content of the proof of Theorem 10, used in Case 3 ($\gamma_i\le1$) of the proof of Theorem 11 with $x=\hat x$ and $y_i=\hat y_i$; the hypotheses hold there because the candidates of Theorem 11 contain every $\hat S_i(\epsilon)$, $N$ and the singletons.
--
--   Differences from the source:
--   - generalization: the step is stated for x = x̂, y_i = ŷ_i with (x̂, ŷ) optimal for (4) with Theorem 10's candidates → arbitrary x ≥ 0 and y_i satisfying the candidate constraints the step uses; reason: specializes to the page at (x̂, ŷ_i)
--   - encoding: (2x̂, 2ŷ) satisfies the second set of constraints for nest i in problem (10) → 2y_i ≥ V_i(S)^γi (R_i(S) − 2x) for all S ⊂ N (the constraint of (3)); reason: the two are equivalent for 2x ≥ 0 and γ_i ≤ 1 by the identity in the proof of Lemma 9; the (3) form is what Case 3 on p. 48 uses
--   - encoding: Ŝ_i(ϵ_i) = {j : ẑ_ij(ϵ_i) = 1}, ẑ_i(ϵ_i) the greedy fill of (11) in revenue order among products with v_ij ≤ ϵ_i → Shat: eligible products (v_ij ≤ ϵ) taken in index order while they fit entirely; the fill stops at the first one that does not fit, so a later zero-weight product is not taken; reason: the page does not say whether zero-weight products after the fractional item get 1; they change neither Σ r v nor V_i, so every constraint value of (3) and (4) is the same under either convention, and under the stop rule Ŝ_i(ϵ) is an N^k_ij as p. 25 asserts
--   - encoding: ϵ_i ∈ [0, ∞] → Ŝ_i(ϵ) for real ϵ ≥ 0, plus N (Finset.univ) for ϵ = ∞; reason: with infinite capacity every product is eligible and fits, so Ŝ_i(∞) = N
--   - reading: r_ij is a revenue; its sign is not stated → hypothesis 0 ≤ r_ij; reason: revenues are nonnegative in the model; the proof of Theorem 11 uses it (p. 45 via p. 46 for x̂ ≥ 0, Case 2 on p. 48, Case 3 on p. 49). Without it Theorem 11 fails: v0 = 0, two nests with v_10 = v_20 = 0, γ = (0.7, 1.5), one product each, r = (−0.956, −0.343), v = (0.536, 0) give β = 2, x̂ = −0.956, ŷ = 0, and the constraint for {1} in nest 1 fails at (βx̂, βŷ)
--   - reading: v_i0, v_ij are preference weights (p. 7 allows v_i0 = 0 and padding products with v_ij = 0) → hypotheses 0 ≤ v_i0, 0 ≤ v_ij (zero allowed); reason: preference weights of a logit model are nonnegative; the remarks on p. 7 allow exactly the zero values
--   - encoding: V_i(S_i)^γi and R_i(S_i) with the interpretation R_i(∅) = 0 → Real.rpow (0^0 = 1, 0^γ = 0 for γ ≠ 0) and division with a/0 = 0; reason: realizes R_i(∅) = 0; the 0^0 case (V_i(S) = 0 = γ_i) is not discussed by the paper and gets Lean's value 1
--   - encoding: products N = {1, …, n} with r_i1 ≥ … ≥ r_in → products Fin n (index 0 is product 1); the ordering is Antitone (r i); 1-based k and j are natural numbers; reason: Lean convention; same instances
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, proof of Theorem 10 (Appendix A.3), eqs. (26)–(29), pp. 45–46; used in the proof of Theorem 11 (Appendix A.4), Case 3, p. 48

import Mathlib
import Definitions.Def_NestedLogitAssort_General_T
import Definitions.Def_NestedLogitAssort_General_Shat

namespace NestedLogitAssort.General

/-- **The factor-two bound of the proof of Theorem 10, for one nest.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, proof of Theorem 10 (Appendix A.3), eqs. (26)–(29), pp. 45–46: "Collecting (28) and (29)
in the two cases, the solution `(2 x̂, 2 ŷ)` satisfies the second set of constraints for nest `i` in
problem (10)"; invoked in Case 3 of the proof of Theorem 11 (Appendix A.4), p. 48.

For a nest with `0 ≤ γ_i ≤ 1` and `x ≥ 0`, if `y_i ≥ V_i(S)^{γ_i}(R_i(S) − x)` for every greedy
assortment `S = Ŝ_i(ϵ)` (`ϵ ≥ 0`), for `S = N` (`ϵ = ∞`) and for every singleton `S = {j}`, then
`2 y_i ≥ V_i(S)^{γ_i}(R_i(S) − 2x)` for every `S ⊂ N`.

**Formalization Note.** On the page `x = x̂ ≥ 0` and `y_i = ŷ_i`; the constraints on `y_i` are those of
(4) for the candidates `{Ŝ_i(ϵ_i) : ϵ_i ∈ [0, ∞]} ∪ {{j} : j ∈ N}`. The conclusion is feasibility for
(3), equivalent to feasibility for (10) by Lemma 9. Hypotheses: `v_{i0}, v_{ij} ≥ 0`,
`r_{ij} ≥ 0`, `r_{i1} ≥ … ≥ r_{in}` (`Antitone`, p. 7), `0 ≤ γ_i ≤ 1`. -/
theorem factor_two_nest {M : Type*} {n : ℕ} (I : Instance M n) (i : M)
    (hγ0 : 0 ≤ I.γ i) (hγ1 : I.γ i ≤ 1) (hw0 : 0 ≤ I.w0 i) (hv : ∀ j, 0 ≤ I.v i j)
    (hr : ∀ j, 0 ≤ I.r i j) (hanti : Antitone (I.r i)) (x yi : ℝ) (hx : 0 ≤ x)
    (hShat : ∀ ε : ℝ, 0 ≤ ε → T I i (Shat I i ε) x ≤ yi)
    (huniv : T I i Finset.univ x ≤ yi) (hsing : ∀ j : Fin n, T I i {j} x ≤ yi) :
    ∀ S : Finset (Fin n), T I i S (2 * x) ≤ 2 * yi := by sorry

end NestedLogitAssort.General
