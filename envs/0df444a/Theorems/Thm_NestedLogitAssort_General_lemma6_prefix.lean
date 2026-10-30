-- Prove2me | Theorems.Thm_NestedLogitAssort_General_lemma6_prefix
-- name    : NestedLogitAssort.General.lemma6_prefix
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:51:01.862403+00:00
-- url     : https://prove2.me/theorems/480a18dd-0314-47cb-abb8-a0efda5b9f82
-- title:
--   Lemma 6 (with $v_{i0}$): a prefix vector maximizes problem (8)
-- statement:
--   Consider the nested logit model with a finite set $M$ of nests, each offering the products $N=\{1,\dots,n\}$ sorted so that $r_{i1}\ge\dots\ge r_{in}$; $v_{ij}$ is the preference weight of product $j$ in nest $i$, $v_{i0}$ that of the no-purchase option inside nest $i$, $v_0$ that of choosing no nest, and $\gamma_i\ge0$ the dissimilarity parameter of nest $i$. Write $V_i(S)=v_{i0}+\sum_{j\in S}v_{ij}$ and $R_i(S)=\sum_{j\in S}r_{ij}v_{ij}/V_i(S)$, with $R_i(\emptyset)=0$.
--
--   Fix a nest $i$ with $n\ge1$, $v_{i0}\ge0$, $v_{ij}\ge0$ and $r_{ij}\ge0$, and any number $x$. There are $k\in\{1,\dots,n\}$ and $\rho\in[0,1]$ such that the prefix vector $z^*$ with $z^*_1=\dots=z^*_{k-1}=1$, $z^*_k=\rho$, $z^*_{k+1}=\dots=z^*_n=0$ maximizes
--
--   $$
--   \Bigl(v_{i0}+\sum_{j\in N}v_{ij}z_j\Bigr)^{\gamma_i}\left[\frac{\sum_{j\in N}r_{ij}v_{ij}z_j}{v_{i0}+\sum_{j\in N}v_{ij}z_j}-x\right]
--   $$
--
--   over all $z\in[0,1]^n$. With $v_{i0}=0$ this is Lemma 6 for problem (8); the proof of Theorem 11 uses it with $v_{i0}$ included, in Cases 1 and 2.
--
--   Differences from the source:
--   - generalization: problem (8) has no no-purchase weight (v_i0 = 0); the proof of Theorem 11 applies "the same idea" with v_i0 → any v_i0 ≥ 0; reason: the case v_i0 = 0 is Lemma 6 as printed; the case v_i0 > 0 is the form used on pp. 47–48
--   - reading: "for some k = 1, …, n" → hypothesis 0 < n; reason: the range k = 1, …, n presupposes n ≥ 1
--   - reading: r_ij is a revenue; its sign is not stated → hypothesis 0 ≤ r_ij; reason: revenues are nonnegative in the model; the proof of Theorem 11 uses it (p. 45 via p. 46 for x̂ ≥ 0, Case 2 on p. 48, Case 3 on p. 49). Without it Theorem 11 fails: v0 = 0, two nests with v_10 = v_20 = 0, γ = (0.7, 1.5), one product each, r = (−0.956, −0.343), v = (0.536, 0) give β = 2, x̂ = −0.956, ŷ = 0, and the constraint for {1} in nest 1 fails at (βx̂, βŷ)
--   - reading: v_i0, v_ij are preference weights (p. 7 allows v_i0 = 0 and padding products with v_ij = 0) → hypotheses 0 ≤ v_i0, 0 ≤ v_ij (zero allowed); reason: preference weights of a logit model are nonnegative; the remarks on p. 7 allow exactly the zero values
--   - encoding: V_i(S_i)^γi and R_i(S_i) with the interpretation R_i(∅) = 0 → Real.rpow (0^0 = 1, 0^γ = 0 for γ ≠ 0) and division with a/0 = 0; reason: realizes R_i(∅) = 0; the 0^0 case (V_i(S) = 0 = γ_i) is not discussed by the paper and gets Lean's value 1
--   - encoding: products N = {1, …, n} with r_i1 ≥ … ≥ r_in → products Fin n (index 0 is product 1); the ordering is Antitone (r i); 1-based k and j are natural numbers; reason: Lean convention; same instances
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, Lemma 6, p. 21; used in the proof of Theorem 11 (Appendix A.4), pp. 47–48

import Mathlib
import Definitions.Def_NestedLogitAssort_General_Fobj
import Definitions.Def_NestedLogitAssort_General_prefixVec

namespace NestedLogitAssort.General

/-- **Lemma 6, with the no-purchase weight `v_{i0}`.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, Lemma 6, p. 21: "There exists an optimal solution `z*_i` to the problem (8) such that
`z*_{i1} = 1, …, z*_{i,k−1} = 1, z*_{ik} ∈ [0, 1], z*_{i,k+1} = 0, …, z*_{in} = 0` for some
`k = 1, …, n`"; used with `v_{i0}` added ("Using the same idea in the proof of Lemma 6") in the proof
of Theorem 11 (Appendix A.4), pp. 47–48.

For every `x`, the maximum of `Fobj I i · x` over `[0, 1]^n` is attained at a prefix vector
`prefixVec k ρ` with `1 ≤ k ≤ n` and `ρ ∈ [0, 1]`.

**Formalization Note.** Hypotheses: `n ≥ 1` (so that `k = 1, …, n` exists), `v_{i0}, v_{ij} ≥ 0`
(p. 7), `r_{ij} ≥ 0`, `r_{i1} ≥ … ≥ r_{in}` (`Antitone`, p. 7), `γ_i ≥ 0` (p. 7). Problem (8)
is the case `v_{i0} = 0`. -/
theorem lemma6_prefix {M : Type*} {n : ℕ} (I : Instance M n) (i : M) (hn : 0 < n)
    (hw0 : 0 ≤ I.w0 i) (hv : ∀ j, 0 ≤ I.v i j) (hr : ∀ j, 0 ≤ I.r i j)
    (hanti : Antitone (I.r i)) (hγ0 : 0 ≤ I.γ i) (x : ℝ) :
    ∃ (k : ℕ) (ρ : ℝ), 1 ≤ k ∧ k ≤ n ∧ 0 ≤ ρ ∧ ρ ≤ 1 ∧
      ∀ z : Fin n → ℝ, (∀ j, 0 ≤ z j ∧ z j ≤ 1) →
        Fobj I i z x ≤ Fobj I i (prefixVec k ρ) x := by sorry

end NestedLogitAssort.General
