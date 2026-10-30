-- Prove2me | Theorems.Thm_NestedLogitAssort_General_case1_bound
-- name    : NestedLogitAssort.General.case1_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:51:30.796732+00:00
-- url     : https://prove2.me/theorems/c542a5b0-fc69-4ab9-b124-b25698bbdae5
-- title:
--   Proof of Theorem 11, Case 1 ($\gamma_i>1$, $\hat y_i\ge0$): eq. (30)
-- statement:
--   Consider the nested logit model with a finite set $M$ of nests, each offering the products $N=\{1,\dots,n\}$ sorted so that $r_{i1}\ge\dots\ge r_{in}$; $v_{ij}$ is the preference weight of product $j$ in nest $i$, $v_{i0}$ that of the no-purchase option inside nest $i$, $v_0$ that of choosing no nest, and $\gamma_i\ge0$ the dissimilarity parameter of nest $i$. Write $V_i(S)=v_{i0}+\sum_{j\in S}v_{ij}$ and $R_i(S)=\sum_{j\in S}r_{ij}v_{ij}/V_i(S)$, with $R_i(\emptyset)=0$.
--
--   Fix a nest $i$ with $\gamma_i>1$, $v_{i0}\ge0$, $v_{ij}\ge0$, $r_{ij}\ge0$. Let $x\ge0$, $y_i\ge0$ and $b\ge1$ satisfy
--
--   1. $y_i\ge V_i(N_{ik})^{\gamma_i}\bigl(R_i(N_{ik})-x\bigr)$ for $k=1,\dots,n$;
--   2. $V_i(N_{ik})\le b\,V_i(N_{i,k-1})$ for every $k$ with $(i,k)$ in the index range of (12) ($k=2,\dots,n$ if $v_{i0}=0$, $k=1,\dots,n$ if $v_{i0}>0$).
--
--   Then
--
--   $$
--   b\,y_i\ \ge\ V_i(S)^{\gamma_i}\bigl(R_i(S)-b\,x\bigr)\qquad\text{for all }S\subseteq N .
--   $$
--
--   In the proof of Theorem 11, $b=\beta$ from (12), $x=\hat x$ and $y_i=\hat y_i$; the first condition holds because $N_{ik}=N^n_{ik}$ is a candidate assortment and the second is the bound $V_i(N_{ik})/V_i(N_{i,k-1})\le\beta$. The conclusion says that $(\beta\hat x,\beta\hat y)$ satisfies the constraints of (3) for nest $i$.
--
--   Differences from the source:
--   - generalization: the step is stated for x = x̂, y_i = ŷ_i and b = β, with (x̂, ŷ) optimal for (4) → arbitrary reals satisfying the constraints the step uses; reason: specializes to the page at (x̂, ŷ_i, β)
--   - encoding: the bound (v_i0 + q_ik)/(v_i0 + q_i,k−1 + v_ik ρ) ≤ V_i(N^n_ik)/V_i(N^n_i,k−1) ≤ β → hypothesis V_i(N_ik) ≤ b · V_i(N_i,k−1) for every listed k; reason: the ratio bound multiplied out; the goal derives it from (12) with positive denominators
--   - reading: r_ij is a revenue; its sign is not stated → hypothesis 0 ≤ r_ij; reason: revenues are nonnegative in the model; the proof of Theorem 11 uses it (p. 45 via p. 46 for x̂ ≥ 0, Case 2 on p. 48, Case 3 on p. 49). Without it Theorem 11 fails: v0 = 0, two nests with v_10 = v_20 = 0, γ = (0.7, 1.5), one product each, r = (−0.956, −0.343), v = (0.536, 0) give β = 2, x̂ = −0.956, ŷ = 0, and the constraint for {1} in nest 1 fails at (βx̂, βŷ)
--   - reading: v_i0, v_ij are preference weights (p. 7 allows v_i0 = 0 and padding products with v_ij = 0) → hypotheses 0 ≤ v_i0, 0 ≤ v_ij (zero allowed); reason: preference weights of a logit model are nonnegative; the remarks on p. 7 allow exactly the zero values
--   - encoding: V_i(S_i)^γi and R_i(S_i) with the interpretation R_i(∅) = 0 → Real.rpow (0^0 = 1, 0^γ = 0 for γ ≠ 0) and division with a/0 = 0; reason: realizes R_i(∅) = 0; the 0^0 case (V_i(S) = 0 = γ_i) is not discussed by the paper and gets Lean's value 1
--   - encoding: products N = {1, …, n} with r_i1 ≥ … ≥ r_in → products Fin n (index 0 is product 1); the ordering is Antitone (r i); 1-based k and j are natural numbers; reason: Lean convention; same instances
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, proof of Theorem 11 (Appendix A.4), Case 1, eq. (30) and the display after it, pp. 47–48

import Mathlib
import Definitions.Def_NestedLogitAssort_General_T
import Definitions.Def_NestedLogitAssort_General_NBR
import Definitions.Def_NestedLogitAssort_General_Listed

namespace NestedLogitAssort.General

/-- **Case 1 of the proof of Theorem 11: `γ_i > 1` and `ŷ_i ≥ 0`.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, proof of Theorem 11 (Appendix A.4), Case 1, eq. (30) and the display after it,
pp. 47–48 (unnumbered): "Therefore, the solution `(β x̂, β ŷ)` satisfies the second set of
constraints for nest `i` in problem (3)."

Let nest `i` have `γ_i > 1`, and let `x ≥ 0`, `y_i ≥ 0` and `b ≥ 1` satisfy
`y_i ≥ V_i(N_{ik})^{γ_i}(R_i(N_{ik}) − x)` for `k = 1, …, n` and
`V_i(N_{ik}) ≤ b V_i(N_{i,k−1})` for every pair `(i, k)` of (12). Then
`b y_i ≥ V_i(S)^{γ_i}(R_i(S) − b x)` for every `S ⊂ N`.

**Formalization Note.** On the page `b = β` (expression (12)), `x = x̂ ≥ 0`, `y_i = ŷ_i`, and the
constraints on `y_i` are those of (4) for `N^n_{ik} = N_{ik}`; the ratio hypothesis is (12)'s bound
`V_i(N_{ik})/V_i(N_{i,k−1}) ≤ β`, multiplied out. Hypotheses: `v_{i0}, v_{ij} ≥ 0`, `r_{ij} ≥ 0`,
`r_{i1} ≥ … ≥ r_{in}` (`Antitone`, p. 7). `k` is the paper's 1-based index. -/
theorem case1_bound {M : Type*} {n : ℕ} (I : Instance M n) (i : M)
    (hγ : 1 < I.γ i) (hw0 : 0 ≤ I.w0 i) (hv : ∀ j, 0 ≤ I.v i j) (hr : ∀ j, 0 ≤ I.r i j)
    (hanti : Antitone (I.r i)) (x yi b : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ yi) (hb : 1 ≤ b)
    (hcon : ∀ k : ℕ, 1 ≤ k → k ≤ n → T I i (NBR n k) x ≤ yi)
    (hratio : ∀ k : ℕ, Listed I i k → V I i (NBR n k) ≤ b * V I i (NBR n (k - 1))) :
    ∀ S : Finset (Fin n), T I i S (b * x) ≤ b * yi := by sorry

end NestedLogitAssort.General
