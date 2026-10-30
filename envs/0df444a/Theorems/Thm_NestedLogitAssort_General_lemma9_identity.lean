-- Prove2me | Theorems.Thm_NestedLogitAssort_General_lemma9_identity
-- name    : NestedLogitAssort.General.lemma9_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:54:15.463947+00:00
-- url     : https://prove2.me/theorems/2087e45f-0056-484f-8f1a-870dc5b2f538
-- title:
--   Proof of Lemma 9: $\max_S V_i(S)^{\gamma_i}(R_i(S)-x)=\max_{\epsilon\ge0}(v_{i0}+\epsilon)^{\gamma_i}[K_i(\epsilon)/(v_{i0}+\epsilon)-x]$
-- statement:
--   Consider the nested logit model with a finite set $M$ of nests, each offering the products $N=\{1,\dots,n\}$ sorted so that $r_{i1}\ge\dots\ge r_{in}$; $v_{ij}$ is the preference weight of product $j$ in nest $i$, $v_{i0}$ that of the no-purchase option inside nest $i$, $v_0$ that of choosing no nest, and $\gamma_i\ge0$ the dissimilarity parameter of nest $i$. Write $V_i(S)=v_{i0}+\sum_{j\in S}v_{ij}$ and $R_i(S)=\sum_{j\in S}r_{ij}v_{ij}/V_i(S)$, with $R_i(\emptyset)=0$.
--
--   Fix a nest $i$ with $0\le\gamma_i\le1$, $v_{i0}\ge0$, $v_{ij}\ge0$, $r_{ij}\ge0$, and let $x\ge0$. Then
--
--   $$
--   \max_{S\subseteq N}V_i(S)^{\gamma_i}\bigl(R_i(S)-x\bigr)\ =\ \max_{\epsilon\ge0}\left\{(v_{i0}+\epsilon)^{\gamma_i}\left[\frac{K_i(\epsilon)}{v_{i0}+\epsilon}-x\right]\right\},
--   $$
--
--   where $K_i(\epsilon)$ is the 0–1 knapsack value (9); in particular the maximum on the right is attained. It turns the constraints of (3) for nest $i$ into the knapsack form (10), on which the factor-two argument of Theorem 10 (Case 3 of the proof of Theorem 11) operates.
--
--   Differences from the source:
--   - encoding: max_{S_i⊂N} … = max_{ϵ_i≥0} {…} → the left maximum is Finset.sup' over all S; it is the greatest element (IsGreatest) of the set of right-hand values over ϵ ≥ 0; reason: IsGreatest states both attainment of the right maximum and equality, with no real supremum
--   - reading: r_ij is a revenue; its sign is not stated → hypothesis 0 ≤ r_ij; reason: revenues are nonnegative in the model; the proof of Theorem 11 uses it (p. 45 via p. 46 for x̂ ≥ 0, Case 2 on p. 48, Case 3 on p. 49). Without it Theorem 11 fails: v0 = 0, two nests with v_10 = v_20 = 0, γ = (0.7, 1.5), one product each, r = (−0.956, −0.343), v = (0.536, 0) give β = 2, x̂ = −0.956, ŷ = 0, and the constraint for {1} in nest 1 fails at (βx̂, βŷ)
--   - reading: v_i0, v_ij are preference weights (p. 7 allows v_i0 = 0 and padding products with v_ij = 0) → hypotheses 0 ≤ v_i0, 0 ≤ v_ij (zero allowed); reason: preference weights of a logit model are nonnegative; the remarks on p. 7 allow exactly the zero values
--   - encoding: V_i(S_i)^γi and R_i(S_i) with the interpretation R_i(∅) = 0 → Real.rpow (0^0 = 1, 0^γ = 0 for γ ≠ 0) and division with a/0 = 0; reason: realizes R_i(∅) = 0; the 0^0 case (V_i(S) = 0 = γ_i) is not discussed by the paper and gets Lean's value 1
--   - generalization: products ordered so that r_i1 ≥ … ≥ r_in (p. 7) → no ordering of the revenues assumed; reason: the identity does not use the ordering; it specializes to the page on ordered instances
--   - encoding: products N = {1, …, n} → products Fin n (index 0 is product 1); 1-based k and j are natural numbers; reason: Lean convention; same instances
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, proof of Lemma 9, p. 23

import Mathlib
import Definitions.Def_NestedLogitAssort_General_T
import Definitions.Def_NestedLogitAssort_General_val10

namespace NestedLogitAssort.General

/-- **The identity in the proof of Lemma 9, for one nest.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, proof of Lemma 9, p. 23 (unnumbered): "the result follows if
we can show that
`max_{S_i ⊂ N} V_i(S_i)^{γ_i}(R_i(S_i) − x) = max_{ϵ_i ≥ 0} {(v_{i0} + ϵ_i)^{γ_i}[K_i(ϵ_i)/(v_{i0} + ϵ_i) − x]}`
for any `x ≥ 0`."

For a nest with `0 ≤ γ_i ≤ 1` and `x ≥ 0`, the maximum over the (finitely many) assortments
`S ⊂ N` of `V_i(S)^{γ_i}(R_i(S) − x)` is the greatest element of the set of values
`(v_{i0} + ϵ)^{γ_i}[K_i(ϵ)/(v_{i0} + ϵ) − x]`, `ϵ ≥ 0`: the maximum on the right is attained and
equals the one on the left.

**Formalization Note.** The left maximum is a `Finset.sup'` over all `S ⊂ N` (always attained); the
right one is stated with `IsGreatest`, so no real supremum is taken. Lemma 9's printed statement
(the optimal solutions of (3) and (10) coincide) is not formalized. The section's assumption
`γ_i ≤ 1` is the Section 5 standing assumption (p. 22) under which Lemma 9 is stated; A.4 uses it in
Case 3 (`γ_i ≤ 1`). Hypotheses: `v_{i0}, v_{ij} ≥ 0`, `r_{ij} ≥ 0`, `0 ≤ γ_i ≤ 1`. -/
theorem lemma9_identity {M : Type*} {n : ℕ} (I : Instance M n) (i : M)
    (hγ0 : 0 ≤ I.γ i) (hγ1 : I.γ i ≤ 1) (hw0 : 0 ≤ I.w0 i) (hv : ∀ j, 0 ≤ I.v i j)
    (hr : ∀ j, 0 ≤ I.r i j) (x : ℝ) (hx : 0 ≤ x) :
    IsGreatest {w : ℝ | ∃ ε : ℝ, 0 ≤ ε ∧ w = val10 I i ε x}
      (Finset.univ.sup' Finset.univ_nonempty (fun S : Finset (Fin n) => T I i S x)) := by sorry

end NestedLogitAssort.General
