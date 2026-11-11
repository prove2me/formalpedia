-- Prove2me | Theorems.Thm_MixedORAM_PublicRead_lemma_A_5
-- name    : MixedORAM.PublicRead.lemma_A_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:45:40.332641+00:00
-- url     : https://prove2.me/theorems/f41eb4da-18f7-492a-bfff-80d36dcc1aef
-- title:
--   Lemma A.5 — per-edge charge: ≤ min{z, ℓ_i, s_i} endpoints, total normalized charge O(1/ρ)
-- statement:
--   Let $\ell_0\ge0$ and $\rho\ge2$ be integers, $\ell_i=\ell_0\rho^i$ and $s_i=(\ell_i-\ell_0)/(\rho-1)$, and for an endpoint $e$ let the epoch be $I_i=[e-s_i-\ell_i+1,\,e-s_i]$ with younger span $[e-s_i+1,\,e]$. Fix a dependency edge between requests $v_1<v_2$ and put $z=v_2-v_1$. Then for each $i$:
--
--   - there are at most $\min\{z,\ell_i,s_i\}$ endpoints $e$ such that the edge starts in $I_i$ and ends in its younger span;
--   - such endpoints exist only if $z\le\ell_i+s_i$.
--
--   Consequently there is a universal constant $C$ with
--   $$\sum_{i:\,z\le\ell_i+s_i}\frac{\min\{z,\ell_i,s_i\}}{\ell_i}\ \le\ \frac C\rho .$$
--
--   Averaged over endpoints, this bounds the normalized charge $\sum_i \mathbb E E_{I_i}/\ell_i$ of Lemma A.6 by $O(T_N/\rho)$.
--
--   Differences from the source:
--   - generalization: a dependency edge of the reference execution between requests v₁ < v₂ → any integers v₁ < v₂, endpoints e ∈ ℤ; reason: the claims involve only the positions; every edge of an execution is such a pair
--   - encoding: s_i = (ℓ_i − ℓ₀)/(ρ − 1); 'at most min{z, ℓ_i, s_i} endpoints' → s_i = ℓ₀ Σ_{j<i} ρ^j; every finite set of such endpoints has at most min{z, ℓ_i, s_i} elements; reason: the same integer; the set of endpoints is finite
--   - encoding: Σ over all epochs i with z ≤ ℓ_i + s_i, = O(1/ρ) → every partial sum over i < K is at most C/ρ for one universal C > 0 (real division, ℓ_i = 0 giving 0 when ℓ₀ = 0); reason: partial sums of a series of nonnegative terms; O(1/ρ) is a constant independent of ℓ₀, ρ, z
-- source:
--   Ciszewski, Ragnoli, Access Cost Tradeoffs in Mixed-Mode Oblivious RAM, STOC 2027 submission (manuscript sha256 a4f849fd…), p. 18, Lemma A.5 (Eq. (17))

import Mathlib

set_option autoImplicit false

namespace MixedORAM.PublicRead

theorem lemma_A_5 :
    ∃ C : ℝ, 0 < C ∧ ∀ (ℓ₀ ρ : ℕ), 2 ≤ ρ → ∀ v₁ v₂ : ℤ, v₁ < v₂ →
      let z : ℤ := v₂ - v₁
      let ℓ : ℕ → ℕ := fun i => ℓ₀ * ρ ^ i
      let s : ℕ → ℕ := fun i => ℓ₀ * ∑ j ∈ Finset.range i, ρ ^ j
      let ok : ℕ → ℤ → Prop := fun i e =>
        e - s i - ℓ i + 1 ≤ v₁ ∧ v₁ ≤ e - s i ∧ e - s i + 1 ≤ v₂ ∧ v₂ ≤ e
      (∀ (i : ℕ) (F : Finset ℤ), (∀ e ∈ F, ok i e) →
          (F.card : ℤ) ≤ min z (min (ℓ i : ℤ) (s i : ℤ))) ∧
        (∀ (i : ℕ) (e : ℤ), ok i e → z ≤ (ℓ i : ℤ) + s i) ∧
        ∀ K : ℕ, ∑ i ∈ (Finset.range K).filter (fun i => z ≤ (ℓ i : ℤ) + s i),
            ((min z (min (ℓ i : ℤ) (s i : ℤ)) : ℤ) : ℝ) / (ℓ i : ℝ) ≤ C / ρ := by sorry

end MixedORAM.PublicRead
