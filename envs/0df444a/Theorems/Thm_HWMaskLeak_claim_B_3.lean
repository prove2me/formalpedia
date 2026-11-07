-- Prove2me | Theorems.Thm_HWMaskLeak_claim_B_3
-- name    : HWMaskLeak.claim_B_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:29:36.820381+00:00
-- url     : https://prove2.me/theorems/38110975-c016-43c3-bb03-40179a17b291
-- title:
--   Claim B.3 — weighted Cauchy–Schwarz for square-root sums
-- statement:
--   Let $\Omega$ be a finite set of indices and $\mathcal T$ a finite set. Let $a_t$, $b_{w,t}$, $\mu_w$ ($w\in\Omega$, $t\in\mathcal T$) be nonnegative reals with $\mu_w=0\Rightarrow b_{w,t}=0$ for every $t$. Put $\Omega^+=\{w\in\Omega:\mu_w>0\}$ and suppose $\alpha\ge0$ satisfies $\sum_{w\in\Omega^+}b_{w,t}/\mu_w\le\alpha$ for every $t$. Then
--   $$
--   \sum_{w\in\Omega}\sqrt{\sum_{t}a_t\,b_{w,t}}\le\alpha^{1/2}\sqrt{\sum_{w\in\Omega}\mu_w}\,\sqrt{\sum_t a_t}.
--   $$
--
--   With $\mu_w=\rho_w(N)$ and $\alpha=\alpha_{\mathrm{bin}}(N)$ it yields the one-share contraction (Lemma 4.4).
--
--   Differences from the source:
--   - generalization: t ranges over the nonzero residues of ℤ/Nℤ → t ranges over an arbitrary finite type τ; reason: the claim and its proof use only finiteness of the index set; τ = {t : ZMod N // t ≠ 0} gives the source's statement
--   - encoding: α^{1/2} → Real.sqrt α; reason: α ≥ 0
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360…), App. B.2, Claim B.3, p.42

import Mathlib

namespace HWMaskLeak

/-- **Claim B.3** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak Their Weight: From Additive Sharing to
Learning with Physical Rounding*, preprint (version of October 31, 2026, sha256 ab686360…), App. B.2, Claim B.3, p.42): let `Ω` be a finite set of indices, let
`a_t, b_{w,t}, μ_w` be nonnegative reals with `μ_w = 0 ⟹ b_{w,t} = 0` for every `t`, put
`Ω⁺ = {w ∈ Ω : μ_w > 0}`, and suppose `α ⩾ 0` satisfies `Σ_{w ∈ Ω⁺} b_{w,t}/μ_w ⩽ α` for every `t`.
Then `Σ_{w ∈ Ω} √(Σ_t a_t b_{w,t}) ⩽ α^{1/2} √(Σ_{w ∈ Ω} μ_w) √(Σ_t a_t)`.

**Formalization Note** The paper's `t` ranges over the nonzero residues of `ℤ/Nℤ`; here it ranges
over an arbitrary finite type `τ`, which specializes to `{t : ZMod N // t ≠ 0}`. `α^{1/2}` is
`Real.sqrt α`. -/
theorem claim_B_3 {ι τ : Type*} [Fintype ι] [Fintype τ] (a : τ → ℝ) (b : ι → τ → ℝ) (μ : ι → ℝ)
    (ha : ∀ t, 0 ≤ a t) (hb : ∀ w t, 0 ≤ b w t) (hμ : ∀ w, 0 ≤ μ w)
    (hμb : ∀ w, μ w = 0 → ∀ t, b w t = 0) (α : ℝ) (hα : 0 ≤ α)
    (hαb : ∀ t, ∑ w ∈ Finset.univ.filter (fun w => 0 < μ w), b w t / μ w ≤ α) :
    ∑ w, Real.sqrt (∑ t, a t * b w t) ≤
      Real.sqrt α * Real.sqrt (∑ w, μ w) * Real.sqrt (∑ t, a t) := by sorry

end HWMaskLeak
