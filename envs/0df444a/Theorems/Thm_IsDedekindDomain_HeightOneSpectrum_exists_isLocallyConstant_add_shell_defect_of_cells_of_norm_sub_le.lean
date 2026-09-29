-- Prove2me | Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_isLocallyConstant_add_shell_defect_of_cells_of_norm_sub_le
-- name    : IsDedekindDomain.HeightOneSpectrum.exists_isLocallyConstant_add_shell_defect_of_cells_of_norm_sub_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/b141080d-5116-5754-a541-9260758f4fdf
-- title:
--   Shell decomposition of a window with logarithmic germ at 1
-- statement:
--   Let $K$ be a number field, $v$ a nonzero prime of $\mathcal O_K$ with completion $K_v$, and let $\Psi : K_v^\times\times K_v^\times\to\mathbb C$ satisfy: $\Psi$ has compact support; at every point $p$ whose second coordinate is $\ne 1$ there is a neighbourhood of $p$ on which $\Psi$ equals $\Psi(p)$; there exist a neighbourhood $U$ of $1$ in $K_v^\times$ and $\rho>0$ with $\Psi(a',t')=\Psi(a,t)$ whenever $t\in U$, $\|a'-a\|\le\rho\|a\|$ and $\|t'-t\|\le\rho\|1-t\|$; and there is $C$ with $\|\Psi(a,t)-\Psi(a,1)\|\le C\|1-t\|\,(1+|\log\|1-t\||)$ for all $a,t$. Then there exist a locally constant, compactly supported $\Psi_0 : K_v^\times\times K_v^\times\to\mathbb C$; subgroups $U_1,A\le K_v^\times$ with $U_1$ open and $A$ open and compact; open subgroups $V_k\le U_1\cap A$ ($k\in\mathbb N$); compact sets $\mathrm{sh}_k\subseteq U_1$ with $1\notin\mathrm{sh}_k$, pairwise disjoint, covering $U_1\setminus\{1\}$, and stable under right multiplication by $V_k$; a finite set $F_a$ of units pairwise inequivalent modulo $A$; an $M_0\in\mathbb N$ and $C'\ge 0$, such that $\Psi(a,t)=\Psi_0(a,t)$ whenever $t$ lies in no shell, and for each $k$ there are a finite set $F_k$ with $|F_k|\le M_0$, pairwise inequivalent modulo $V_k$, and coefficients $c(\alpha,\tau)$ with $\|c(\alpha,\tau)\|\le C'(k+1)\,N(v)^{-k}$, such that for $t\in\mathrm{sh}_k$, $\Psi(a,t)=\Psi_0(a,t)+\sum_{\alpha\in F_a}\sum_{\tau\in F_k}c(\alpha,\tau)\,\mathbf 1[a^{-1}\alpha\in A]\,\mathbf 1[t^{-1}\tau\in V_k]$. Here $N(v)$ is the absolute norm of the prime $v$.
--
--   This is the local non-archimedean input that converts a function on $K_v^\times\times K_v^\times$ which is locally constant away from the diagonal condition $t=1$, but only continuous with a logarithmic germ at $t=1$, into a genuinely locally constant function plus defect terms supported on the annuli $\mathrm{sh}_k$ around $1$, each defect being a finite step function on cosets of $A$ and $V_k$ with coefficients decaying like $(k+1)N(v)^{-k}$; the underlying system of subgroups and shells is produced by [`IsDedekindDomain.HeightOneSpectrum.exists_subgroups_shells_finset_card_le_of_units_adicCompletion`](thm.html#IsDedekindDomain.HeightOneSpectrum.exists_subgroups_shells_finset_card_le_of_units_adicCompletion). It feeds the global statement [`NumberField.exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_discWindow_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_forall_eq_of_norm_sub_le`](thm.html#NumberField.exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_discWindow_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_forall_eq_of_norm_sub_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_exists_isLocallyConstant_add_shell_defect_of_cells_of_norm_sub_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

open scoped Classical in

theorem IsDedekindDomain.HeightOneSpectrum.exists_isLocallyConstant_add_shell_defect_of_cells_of_norm_sub_le
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (Ψ : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ)
    (hcs : HasCompactSupport Ψ)
    (hlc : ∀ p : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ, p.2 ≠ 1 → ∃ U ∈ nhds p, ∀ q ∈ U, Ψ q = Ψ p)
    (hcells : ∃ U ∈ nhds (1 : (v.adicCompletion K)ˣ), ∃ ρ : ℝ, 0 < ρ ∧
      ∀ a a' t t' : (v.adicCompletion K)ˣ, t ∈ U →
        ‖(a' : (v.adicCompletion K)) - (a : (v.adicCompletion K))‖ ≤ ρ * ‖(a : (v.adicCompletion K))‖ →
        ‖(t' : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ ≤ ρ * ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ →
          Ψ (a', t') = Ψ (a, t))
    (hgerm : ∃ C : ℝ, ∀ a t : (v.adicCompletion K)ˣ,
      ‖Ψ (a, t) - Ψ (a, 1)‖ ≤ C * ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ *
        (1 + |Real.log ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖|)) :
    ∃ (Ψ₀ : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ), IsLocallyConstant Ψ₀ ∧ HasCompactSupport Ψ₀ ∧
    ∃ (U₁ A : Subgroup (v.adicCompletion K)ˣ), IsOpen (U₁ : Set (v.adicCompletion K)ˣ) ∧ IsOpen (A : Set (v.adicCompletion K)ˣ) ∧ IsCompact (A : Set (v.adicCompletion K)ˣ) ∧
    ∃ (V : ℕ → Subgroup (v.adicCompletion K)ˣ), (∀ k, IsOpen (V k : Set (v.adicCompletion K)ˣ)) ∧ (∀ k, V k ≤ U₁) ∧ (∀ k, V k ≤ A) ∧
    ∃ (sh : ℕ → Set (v.adicCompletion K)ˣ),
      (∀ k, sh k ⊆ (U₁ : Set (v.adicCompletion K)ˣ)) ∧ (∀ k, IsCompact (sh k)) ∧ (∀ k, (1 : (v.adicCompletion K)ˣ) ∉ sh k) ∧
      (Pairwise fun k k' => Disjoint (sh k) (sh k')) ∧
      (∀ t : (v.adicCompletion K)ˣ, t ∈ U₁ → t ≠ 1 → ∃ k, t ∈ sh k) ∧
      (∀ k, ∀ t ∈ sh k, ∀ τ ∈ V k, t * τ ∈ sh k) ∧
    ∃ (Fa : Finset (v.adicCompletion K)ˣ), (∀ α ∈ Fa, ∀ α' ∈ Fa, α ≠ α' → α⁻¹ * α' ∉ A) ∧
    ∃ (M₀ : ℕ) (C' : ℝ), 0 ≤ C' ∧
      (∀ a t : (v.adicCompletion K)ˣ, (∀ k, t ∉ sh k) → Ψ (a, t) = Ψ₀ (a, t)) ∧
      (∀ k, ∃ (Ft : Finset (v.adicCompletion K)ˣ) (c : (v.adicCompletion K)ˣ → (v.adicCompletion K)ˣ → ℂ), Ft.card ≤ M₀ ∧
        (∀ τ ∈ Ft, ∀ τ' ∈ Ft, τ ≠ τ' → τ⁻¹ * τ' ∉ V k) ∧
        (∀ α τ, ‖c α τ‖ ≤ C' * ((k : ℝ) + 1) * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(k : ℤ))) ∧
        ∀ a t : (v.adicCompletion K)ˣ, t ∈ sh k →
          Ψ (a, t) = Ψ₀ (a, t) +
            ∑ α ∈ Fa, ∑ τ ∈ Ft, c α τ * (if a⁻¹ * α ∈ A ∧ t⁻¹ * τ ∈ V k then 1 else 0)) := by sorry
