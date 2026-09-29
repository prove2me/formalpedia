-- Prove2me | Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_subgroups_shells_finset_card_le_of_units_adicCompletion
-- name    : IsDedekindDomain.HeightOneSpectrum.exists_subgroups_shells_finset_card_le_of_units_adicCompletion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/e8e835e5-b56e-5137-bac1-460b2b154d78
-- title:
--   Shells and uniform cell counts in higher unit groups of Kᵥ^×
-- statement:
--   Let $K$ be a number field, $v$ a nonzero prime of its ring of integers $\mathcal O_K$, and let $q =$ `Ideal.absNorm v.asIdeal` be the absolute norm of the corresponding prime ideal; let $n_0, c$ be natural numbers with $n_0 \ge 1$ and $c \ge 1$. The assertion is the existence of subgroups $U_1$ and $A$ of the unit group $(K_v)^\times$ of the $v$-adic completion, a family of subgroups $V_k$ indexed by $k \in \mathbb N$, a family of subsets $\mathrm{sh}_k \subseteq (K_v)^\times$, and a natural number $M_0$, with the following properties. The sets $U_1$ and $A$ are open and compact and each $V_k$ is open, with $V_k \le U_1$ and $V_k \le A$; membership is characterised by the $v$-adic norm on $K_v$, namely $t \in U_1$ iff $\|t - 1\| \le q^{-n_0}$, $a \in A$ iff $\|a - 1\| \le q^{-c}$, and $\tau \in V_k$ iff $\|\tau - 1\| \le q^{-(k + n_0 + c)}$, while $t \in \mathrm{sh}_k$ iff $\|1 - t\| = q^{-(k + n_0)}$. Every $t \in U_1$ has $\|t\| = 1$. Each shell $\mathrm{sh}_k$ is compact, contained in $U_1$ and avoids $1$; the shells are pairwise disjoint and every $t \in U_1$ with $t \ne 1$ lies in some $\mathrm{sh}_k$; and $\mathrm{sh}_k$ is stable under right multiplication by $V_k$. Uniformly in $k$ there is a finite set $F_k \subseteq \mathrm{sh}_k$ of cardinality at most $M_0$ whose elements are pairwise inequivalent modulo $V_k$ (that is, $\tau^{-1}\tau' \notin V_k$ for distinct $\tau, \tau' \in F_k$) and such that every $t \in \mathrm{sh}_k$ satisfies $t^{-1}\tau \in V_k$ for some $\tau \in F_k$. Finally, for every compact $S \subseteq (K_v)^\times$ there is a finite set $F_a$ of units, pairwise inequivalent modulo $A$, such that every $a \in S$ satisfies $a^{-1}\alpha \in A$ for some $\alpha \in F_a$.
--
--   This packages the standard filtration by higher unit groups of a nonarchimedean local field, together with the decomposition of $U_1 \setminus \{1\}$ into norm shells and a count of $V_k$-cells per shell that is bounded independently of $k$. It is used in the local analysis of defects of locally constant functions on $K_v^\times$ and in the adelic integration step that expresses a sum over units as a product of local contributions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_exists_subgroups_shells_finset_card_le_of_units_adicCompletion.lean

import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem IsDedekindDomain.HeightOneSpectrum.exists_subgroups_shells_finset_card_le_of_units_adicCompletion
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (n₀ c : ℕ) (hn₀ : 1 ≤ n₀) (hc : 1 ≤ c) :
    ∃ (U₁ A : Subgroup (v.adicCompletion K)ˣ) (V : ℕ → Subgroup (v.adicCompletion K)ˣ) (sh : ℕ → Set (v.adicCompletion K)ˣ) (M₀ : ℕ),
      IsOpen (U₁ : Set (v.adicCompletion K)ˣ) ∧ IsCompact (U₁ : Set (v.adicCompletion K)ˣ) ∧
      IsOpen (A : Set (v.adicCompletion K)ˣ) ∧ IsCompact (A : Set (v.adicCompletion K)ˣ) ∧
      (∀ k, IsOpen (V k : Set (v.adicCompletion K)ˣ)) ∧ (∀ k, V k ≤ U₁) ∧ (∀ k, V k ≤ A) ∧
      (∀ t : (v.adicCompletion K)ˣ, t ∈ U₁ ↔ ‖(t : (v.adicCompletion K)) - 1‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-(n₀ : ℤ))) ∧
      (∀ a : (v.adicCompletion K)ˣ, a ∈ A ↔ ‖(a : (v.adicCompletion K)) - 1‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-(c : ℤ))) ∧
      (∀ (k : ℕ) (τ : (v.adicCompletion K)ˣ), τ ∈ V k ↔
        ‖(τ : (v.adicCompletion K)) - 1‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-((k + n₀ + c : ℕ) : ℤ))) ∧
      (∀ (k : ℕ) (t : (v.adicCompletion K)ˣ), t ∈ sh k ↔
        ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-((k + n₀ : ℕ) : ℤ))) ∧
      (∀ t : (v.adicCompletion K)ˣ, t ∈ U₁ → ‖(t : (v.adicCompletion K))‖ = 1) ∧
      (∀ k, IsCompact (sh k)) ∧ (∀ k, sh k ⊆ (U₁ : Set (v.adicCompletion K)ˣ)) ∧ (∀ k, (1 : (v.adicCompletion K)ˣ) ∉ sh k) ∧
      (Pairwise fun k k' => Disjoint (sh k) (sh k')) ∧
      (∀ t : (v.adicCompletion K)ˣ, t ∈ U₁ → t ≠ 1 → ∃ k, t ∈ sh k) ∧
      (∀ k, ∀ t ∈ sh k, ∀ τ ∈ V k, t * τ ∈ sh k) ∧
      (∀ k, ∃ Ft : Finset (v.adicCompletion K)ˣ, Ft.card ≤ M₀ ∧ (↑Ft ⊆ sh k) ∧
        (∀ τ ∈ Ft, ∀ τ' ∈ Ft, τ ≠ τ' → τ⁻¹ * τ' ∉ V k) ∧
        ∀ t ∈ sh k, ∃ τ ∈ Ft, t⁻¹ * τ ∈ V k) ∧
      (∀ S : Set (v.adicCompletion K)ˣ, IsCompact S → ∃ Fa : Finset (v.adicCompletion K)ˣ,
        (∀ α ∈ Fa, ∀ α' ∈ Fa, α ≠ α' → α⁻¹ * α' ∉ A) ∧ ∀ a ∈ S, ∃ α ∈ Fa, a⁻¹ * α ∈ A) := by sorry
