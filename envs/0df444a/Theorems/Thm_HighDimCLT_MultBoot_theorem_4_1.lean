-- Prove2me | Theorems.Thm_HighDimCLT_MultBoot_theorem_4_1
-- name    : HighDimCLT.MultBoot.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:38:36.609982+00:00
-- url     : https://prove2.me/theorems/ecdfa1c1-d402-4ba2-b394-e51b1bc1e6de
-- title:
--   Theorem 4.1, p. 2318 — ρ^MB_n(𝒜) ≤ C{Δ̄_n^{1/3} log^{2/3}(pn) + n⁻¹ log^{1/2}(pn)} on Δ_n(𝒜) ≤ Δ̄_n for 𝒜 ⊂ 𝒜^si(a, d) with (M.1′)
-- statement:
--   **Abstract multiplier bootstrap theorem for simple convex sets.** Let $a,b,d>0$. There is a constant $C>0$, depending only on $a$, $b$ and $d$, such that the following holds.
--
--   Let $n\ge4$ and $p\ge3$. Let $X_1,\dots,X_n$ be independent centred random vectors in $\mathbb R^p$ with $\mathrm E[X_{ij}^2]<\infty$, and $Y_1,\dots,Y_n$ independent with $Y_i\sim N(0,\mathrm E[X_iX_i'])$; let $S_n^Y=n^{-1/2}\sum_iY_i$. Let $e_1,\dots,e_n$ be i.i.d. $N(0,1)$, independent of $X_1^n$, and $S_n^{eX}=n^{-1/2}\sum_ie_i(X_i-\bar X)$. Let $\widehat\Sigma=n^{-1}\sum_i(X_i-\bar X)(X_i-\bar X)'$ and $\Sigma=n^{-1}\sum_i\mathrm E[X_iX_i']$.
--
--   Let $\mathcal A$ be a class of Borel sets in $\mathbb R^p$ such that each $A\in\mathcal A$ comes with a polyhedron $A^m(A)=\bigcap_{v\in\mathcal V(A^m)}\{w:w'v\le s(v)\}$, given by a set $\mathcal V(A^m)$ of $m\le(pn)^d$ unit vectors, with
--   1. condition (C): $A^m(A)\subseteq A\subseteq A^{m,a/n}(A)$, where $A^{m,\epsilon}=\bigcap_{v}\{w:w'v\le s(v)+\epsilon\}$;
--   2. condition (M.1′): $n^{-1}\sum_{i=1}^n\mathrm E[(v'X_i)^2]\ge b$ for every $v\in\mathcal V(A^m(A))$.
--
--   Then for every constant $\bar\Delta_n>0$, on the event
--   $$\Delta_n(\mathcal A)=\sup_{A\in\mathcal A}\max_{v_1,v_2\in\mathcal V(A^m(A))}|v_1'(\widehat\Sigma-\Sigma)v_2|\le\bar\Delta_n,$$
--   we have
--   $$\rho_n^{MB}(\mathcal A)=\sup_{A\in\mathcal A}\big|P(S_n^{eX}\in A\mid X_1^n)-P(S_n^Y\in A)\big|\le C\big\{\bar\Delta_n^{1/3}\log^{2/3}(pn)+n^{-1}\log^{1/2}(pn)\big\}.$$
--
--   The theorem says that the Gaussian multiplier bootstrap reproduces the law of $S_n^Y$ on simple convex sets, with an error governed by how well $\widehat\Sigma$ estimates $\Sigma$ in the directions of the facet normals, and only logarithmically by the dimension $p$.
--
--   **Formalization Note**
--   1. "On the event" is read per realization: for every $\omega$ at which the event holds, the bound holds for the law of $S^{eX}_n$ with the data fixed at $X(\omega)$ and $e\sim N(0,I_n)$. Because $e$ is independent of $X_1^n$, this law is a version of the conditional law, so the statement covers every version at once.
--   2. The suprema over $\mathcal A$ and over $v_1,v_2$ are stated as bounds for every member; $\mathcal A$ is an indexed family $(A_k)_{k\in\iota}$ with its chosen $A^m(A_k)$.
--   3. The page takes $\mathcal V(A^m)$ to be the outward facet normals and $s(v)=\mathcal S_{A^m}(v)$ the support values; the statement allows any finite set of unit vectors with any real thresholds, which contains every $m$-generated polytope's representation, so it implies the page's theorem.
--   4. The constant $C$ is chosen after $a,b,d$ and before $n$, $p$, the probability space, the laws, the class, $\bar\Delta_n$ and the realization.
-- source:
--   Chernozhukov, Chetverikov and Kato, Central limit theorems and bootstrap in high dimensions, Ann. Probab. 45 (2017), p. 2318, Theorem 4.1 (with §3.1, p. 2315, condition (C) and (M.1′); §4.1, p. 2318, Σ̂, Σ, Δ_n(𝒜))

import Mathlib
import Definitions.Def_HighDimCLT_MultBoot_Setting

namespace HighDimCLT.MultBoot

open MeasureTheory ProbabilityTheory

universe u

/-- **Theorem 4.1** (Abstract multiplier bootstrap theorem for simple convex sets), p. 2318.
Let `a, b, d > 0`. There is `C > 0` depending only on `a, b, d` such that the following holds.
Let `𝒜 = {A_k}` be a class of Borel sets in `ℝ^p`, each with an approximating polyhedron
`A^m(A_k) = ⋂_{v ∈ V_k} {w : w′v ≤ s_k(v)}` given by `m ≤ (pn)^d` unit vectors, such that
`A^m ⊆ A_k ⊆ A^{m,a/n}` (condition (C)) and `n^{-1} ∑_i E[(v′X_i)²] ≥ b` for every `v ∈ V_k`
((M.1′)). Then for every `Δ̄_n > 0`, at every realization of the data on the event
`Δ_n(𝒜) = sup_k max_{v₁,v₂ ∈ V_k} |v₁′(Σ̂ − Σ)v₂| ≤ Δ̄_n`,
`|P(S^{eX}_n ∈ A_k | X₁ⁿ) − P(S^Y_n ∈ A_k)| ≤ C(Δ̄_n^{1/3} log^{2/3}(pn) + n^{-1} log^{1/2}(pn))`
for every `k`. -/
theorem theorem_4_1 : ∀ a b d : ℝ, 0 < a → 0 < b → 0 < d → ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (n p : ℕ),
    4 ≤ n → 3 ≤ p → ∀ (X Y : Fin n → Ω → EuclideanSpace ℝ (Fin p)), Standing P X Y →
    ∀ {ι : Type u} (A : ι → Set (EuclideanSpace ℝ (Fin p)))
      (V : ι → Finset (EuclideanSpace ℝ (Fin p))) (s : ι → EuclideanSpace ℝ (Fin p) → ℝ),
    (∀ k, MeasurableSet (A k)) →
    (∀ k, ∀ v ∈ V k, ‖v‖ = 1) →
    (∀ k, ((V k).card : ℝ) ≤ ((p : ℝ) * n) ^ d) →
    (∀ k, polyhedron (V k) (s k) ⊆ A k ∧ A k ⊆ enlarge (V k) (s k) (a / n)) →
    (∀ k, ∀ v ∈ V k, b ≤ (∑ i, ∫ ω, inner ℝ v (X i ω) ^ 2 ∂P) / n) →
    ∀ Δbar : ℝ, 0 < Δbar → ∀ ω : Ω,
    (∀ k, ∀ v₁ ∈ V k, ∀ v₂ ∈ V k,
      |quadForm (SigmaHat (fun i => X i ω) - Sigma P X) v₁ v₂| ≤ Δbar) →
    ∀ k, |(mbLaw (fun i => X i ω)).real (A k) - P.real {ω' | normSum Y ω' ∈ A k}|
      ≤ C * (Δbar ^ (1 / 3 : ℝ) * Real.log ((p : ℝ) * n) ^ (2 / 3 : ℝ)
        + Real.sqrt (Real.log ((p : ℝ) * n)) / n) := by sorry

end HighDimCLT.MultBoot
