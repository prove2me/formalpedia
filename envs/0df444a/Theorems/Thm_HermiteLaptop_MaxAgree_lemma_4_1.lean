-- Prove2me | Theorems.Thm_HermiteLaptop_MaxAgree_lemma_4_1
-- name    : HermiteLaptop.MaxAgree.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:17:40.890623+00:00
-- url     : https://prove2.me/theorems/03679239-9202-4cf8-be4c-f33d29a5a0f7
-- title:
--   Lemma 4.1 — edge-wise analysis: the positive- and negative-edge inequalities (24) give expected approximation ratio γ
-- statement:
--   Consider a special case of the general clustering problem: a weighted edge-labelled instance and a family $\mathcal F$ of feasible clusterings, with $\mathrm{OPT}=\max_{\mathcal C\in\mathcal F}\mathrm{val}(\mathcal C)$. Let $a\in[-1/2,0]$, suppose $\mathrm{SDP}(a)$ is a relaxation of the problem, and let $(v^*_i)$ be an optimal solution of $\mathrm{SDP}(a)$. Suppose a mixture of $k$-spokes roundings applied to $(v^*_i)$ always returns a feasible clustering. If for some $\gamma\ge0$ its collision probability satisfies
--   $$P(\rho)\ge\gamma\,s^+_a(\rho)\ \text{ for all }\rho\in[a,1]\qquad\text{and}\qquad 1-P(a)\ge\gamma,\tag{24}$$
--   then the rounding has expected approximation ratio $\gamma$: $\mathbb E[\mathrm{val}(\mathcal C_{\mathrm{ALG}})]\ge\gamma\cdot\mathrm{OPT}$, the expectation over the mixture's randomness.
--
--   **Formalization Note.** $\mathcal F$ is a set of labellings; "relaxation" is `∀ C ∈ F, val C ≤ sdpObj a v*`; "always feasible" is: for every `k` with `λ_k ≠ 0` and every spoke outcome `g`, `kSpokes v* g ∈ F`. The conclusion is `γ * val C ≤ Mixture.value I v*` for every `C ∈ F`.
--
--   Differences from the source:
--   - generalization: F a family of clusterings (partitions of V) → F an arbitrary set of labellings Fin n → ℕ; reason: the family of partitions corresponds to the set of labellings inducing them; arbitrary sets include those
--   - generalization: SDP(a) is a relaxation of the problem → val(C) ≤ SDP(a)-objective of v* for every C ∈ F, i.e. OPT ≤ OPT_SDP; reason: the proof uses only OPT_SDP ≥ OPT; every relaxation in the usual sense satisfies it
--   - reading: the mixture always returns a feasible solution → for every k with λ_k ≠ 0 and every outcome of the spokes, the k-spokes labelling lies in F; reason: the mixture only runs k-spokes with λ_k > 0
--   - encoding: expected approximation ratio γ: E[val(C_ALG)] ≥ γ·OPT → γ·val(C) ≤ Σ_k λ_k E[val(k-spokes(v*))] for every C ∈ F; reason: val takes finitely many values, so OPT is attained and the two are equivalent; the mixture expectation by total probability
-- source:
--   García-Soriano, Miyauchi, Hermite Brings a Laptop, arXiv:2609.35453 (held version, sha256 97504f90…), p. 26 (PDF 29), Lemma 4.1

import Mathlib
import Definitions.Def_HermiteLaptop_MaxAgree_Instance
import Definitions.Def_HermiteLaptop_MaxAgree_Mixture

namespace HermiteLaptop.MaxAgree

/-- Lemma 4.1 (edge-wise analysis): for a clustering problem with feasible family `F`, `a ∈
[−1/2, 0]`, `SDP(a)` a relaxation, `v` optimal for `SDP(a)`, and a mixture whose k-spokes
outputs on `v` are always feasible, the inequalities (24) `P(ρ) ≥ γ s⁺_a(ρ)` on `[a, 1]` and
`1 − P(a) ≥ γ` give `E[val] ≥ γ · val(C)` for every feasible clustering `C`. -/
theorem lemma_4_1 {n : ℕ} (I : Instance n) (F : Set (Fin n → ℕ)) (a : ℝ)
    (ha : a ∈ Set.Icc (-1 / 2 : ℝ) 0) (v : Fin n → EuclideanSpace ℝ (Fin n))
    (hv : I.SDPOptimal a v) (hrelax : ∀ C ∈ F, I.val C ≤ I.sdpObj a v) (μ : Mixture)
    (hfeas : ∀ k : ℕ, μ.lam k ≠ 0 → ∀ g : Fin k → EuclideanSpace ℝ (Fin n), kSpokes v g ∈ F)
    (γ : ℝ) (hγ : 0 ≤ γ)
    (hpos : ∀ ρ ∈ Set.Icc a 1, γ * sPlus a ρ ≤ μ.collision ρ)
    (hneg : γ ≤ 1 - μ.collision a) :
    ∀ C ∈ F, γ * I.val C ≤ μ.value I v := by sorry

end HermiteLaptop.MaxAgree
