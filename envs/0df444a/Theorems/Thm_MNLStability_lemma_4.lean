-- Prove2me | Theorems.Thm_MNLStability_lemma_4
-- name    : MNLStability.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:31:40.893155+00:00
-- url     : https://prove2.me/theorems/5cb112c3-b3f3-4a0f-8428-6092ca279560
-- title:
--   Lemma 4 — swapping in one universal vector per class keeps a $(1-\varepsilon)$ fraction
-- statement:
--   Let $W_1,\dots,W_K$ be pairwise-disjoint classes of products covering $[n]$, each with uniform preference weights, and let $\mathcal U_k$ be $W_k$-universal with accuracy $\varepsilon$ for $k=1,\dots,K$ (with non-negative prices and a finitely supported law of $M$). For every vector $U$ with at most $C$ units there are $V_1\in\mathcal U_1,\dots,V_K\in\mathcal U_K$ such that $\tilde U=(\cdots((U\hookleftarrow_1V_1)\hookleftarrow_2V_2)\cdots\hookleftarrow_KV_K)$ satisfies
--
--   $$\mathbb E[R(\tilde U)]\ \ge\ (1-\varepsilon)\cdot\mathbb E[R(U)]\qquad\text{and}\qquad\|\tilde U\|_1\le C.$$
--
--   The paper states it for the rounded weights $w^\downarrow$ and an optimal vector $U^*$; since $\tilde U$ is determined by the choice of $V_1,\dots,V_K$, enumerating these choices finds it without knowing $U^*$.
--
--   Differences from the source:
--   - generalization: the standing assumption of §2.3, p.13 ("in the remainder of this paper, we operate under the opposite scenario of w_max > εw₀/n") → no regime hypothesis; reason: the proof uses no lower bound on purchase probabilities; every instance of the regime is covered
--   - generalization: the rounded weights w↓, the optimal vector U*, and the families of Theorem 3 → any positive weights, any vector U with at most C units, and any families that are W_k-universal; reason: the argument (p.16) uses only universality of each family and uniform weights on each class
--   - encoding: the classes W₁, …, W_K and families 𝒰₁, …, 𝒰_K → a list of (class, family) pairs, pairwise disjoint and covering [n]; reason: Lean convention; same instances
--   - encoding: the number of customers M, finitely supported (p.3) → a law pM : ℕ →₀ ℝ (IsLaw) mixed over its support; reason: Lean convention; same instances
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), Lemma 4, p.16

import Mathlib
import Definitions.Def_MNLStability_IsLaw
import Definitions.Def_MNLStability_expX
import Definitions.Def_MNLStability_opt
import Definitions.Def_MNLStability_swap
import Definitions.Def_MNLStability_IsUniversal

namespace MNLStability

/-- **Lemma 4** (SSRN:3498325, p.16). Let `W₁, …, W_K` be pairwise-disjoint classes of products that
cover `[n]`, each with uniform weights, and let `𝒰₁, …, 𝒰_K` be families such that `𝒰_k` is
`W_k`-universal with accuracy `ε`. For every vector `U` with at most `C` units there exist
`V₁ ∈ 𝒰₁, …, V_K ∈ 𝒰_K` such that `Ũ = (⋯((U ↩₁ V₁) ↩₂ V₂)⋯ ↩_K V_K)` satisfies
`E[R(Ũ)] ≥ (1 − ε)·E[R(U)]` and `‖Ũ‖₁ ≤ C`. The paper states it for the weights `w↓` and an optimal
vector `U*`. -/
theorem lemma_4 {n : ℕ} (wts : Weights n) (hw : wts.Pos) (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (pM : ℕ →₀ ℝ) (hM : IsLaw pM) (C : ℕ) (ε : ℝ) (hε : 0 < ε)
    (cls : List (Finset (Fin n) × List (Fin n → ℕ)))
    (hdisj : (cls.map Prod.fst).Pairwise Disjoint) (hcover : ∀ i, ∃ p ∈ cls, i ∈ p.1)
    (hunif : ∀ p ∈ cls, wts.UniformOn p.1)
    (huniv : ∀ p ∈ cls, IsUniversal wts r pM C ε p.1 p.2)
    (U : Fin n → ℕ) (hU : norm1 U ≤ C) :
    ∃ Vs : List (Fin n → ℕ), List.Forall₂ (fun p V => V ∈ p.2) cls Vs ∧
      (1 - ε) * expR wts r pM U ≤
        expR wts r pM ((cls.zip Vs).foldl (fun U' q => swap q.1.1 U' q.2) U) ∧
      norm1 ((cls.zip Vs).foldl (fun U' q => swap q.1.1 U' q.2) U) ≤ C := by sorry

end MNLStability
