-- Prove2me | Theorems.Thm_MeanBudgetXC_appendix_C_1_padding
-- name    : MeanBudgetXC.appendix_C_1_padding
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:38:43.769229+00:00
-- url     : https://prove2.me/theorems/f4bde245-a6fb-406b-b646-58b8b68e3cf2
-- title:
--   Appendix C.1, Eqs. (49) and (15) — triangle-free padding and integer parameters
-- statement:
--   1. For every $\theta\in(0,1)$ there is a finite triangle-free graph $T$ with minimum vertex-cover size $v$, order $t$ and
--   $$\rho:=v/t>\max\{\theta,1/2\}.$$
--   2. For such a $T$, put $\delta=1-\theta/\rho$ and fix a positive rational $\eta\le\min\{\theta/16,\delta/32\}$. For every sufficiently large $N$, with $d=\lfloor\theta N\rfloor$, $n_0=\lfloor\eta N\rfloor$, $\ell=\lfloor(d-4n_0)/v\rfloor$, $c=d-4n_0-v\ell$ and $n_{\mathrm{iso}}=N-8n_0-t\ell-2c$, these are nonnegative integers with $0\le c<v$ and $n_0\ge\eta N/2$, they satisfy
--   $$N=8n_0+t\ell+2c+n_{\mathrm{iso}},\qquad d=4n_0+v\ell+c,$$
--   and the degree condition $d-1\ge2\max\{2n_0+1,\Delta(T),2\}$ of Section 4.3 holds.
--
--   These parameters make the host graph fit at every fixed interior density.
--
--   **Formalization Note** $v$ is Mathlib's `vertexCoverNum`, finite for a finite graph. The threshold on $N$ may depend on $\theta$, $T$ and $\eta$.
--
--   Differences from the source:
--   - generalization: a triangle-free padding graph $T$ in the second clause → any graph $T$ on $t$ vertices with $\rho>\max\{\theta,1/2\}$; reason: the arithmetic never uses triangle-freeness; the paper's $T$ is a special case
--   - reading: $n_0=\Omega_\theta(N)$ → $n_0\ge\eta N/2$ for all sufficiently large $N$; reason: this is the explicit form the paper states on p.21
--   - encoding: $n_{\mathrm{iso}}$ is a nonnegative integer → the inequality $8n_0+t\ell+2c\le N$, with $n_{\mathrm{iso}}$ the natural-number difference; reason: natural-number subtraction is then exact
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Section 4.2, display (15), p.18; Section 4.3, p.19; Appendix C.1, display (49), pp.40–41

import Mathlib

namespace MeanBudgetXC

/-- **Appendix C.1, (49) and (15)** (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local
Pair Marginals*, STOC 2027 submission, manuscript sha256 882d9c71…9e76, Section 4.2, p.18;
Section 4.3, p.19; Appendix C.1, pp.40–41).
1. (49) For every `θ ∈ (0, 1)` there is a finite triangle-free graph `T` with minimum
   vertex-cover size `v`, order `t` and `ρ := v/t > max{θ, 1/2}`.
2. (15) For such a `T`, put `δ = 1 − θ/ρ` and fix a positive rational `η ≤ min{θ/16, δ/32}`. For
   every sufficiently large `N`, with `d = ⌊θN⌋`, `n₀ = ⌊ηN⌋`, `ℓ = ⌊(d − 4n₀)/v⌋`,
   `c = d − 4n₀ − vℓ` and `n_iso = N − 8n₀ − tℓ − 2c`, these are nonnegative integers with
   `0 ≤ c < v`, `n₀ ≥ ηN/2`, `N = 8n₀ + tℓ + 2c + n_iso` and `d = 4n₀ + vℓ + c`; and the degree
   condition `d − 1 ≥ 2 max{2n₀ + 1, Δ(T), 2}` of Section 4.3 holds.

**Formalization Note** `v` is Mathlib's `vertexCoverNum`, finite for a finite graph. `n_iso ≥ 0`
is the inequality `8n₀ + tℓ + 2c ≤ N`, after which `n_iso` is the natural-number difference.
Clause 2 is stated for every graph `T` with `ρ > max{θ, 1/2}` (triangle-freeness is not used by
the arithmetic); "sufficiently large" is `∃ N₁, ∀ N ≥ N₁`, with `N₁` depending on `θ, T, η`. -/
theorem appendix_C_1_padding :
    (∀ θ : ℝ, 0 < θ → θ < 1 → ∃ (t : ℕ) (T : SimpleGraph (Fin t)), T.CliqueFree 3 ∧
        max θ (1 / 2) < (T.vertexCoverNum.toNat : ℝ) / t) ∧
      ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ (t : ℕ) (T : SimpleGraph (Fin t)) [DecidableRel T.Adj],
        max θ (1 / 2) < (T.vertexCoverNum.toNat : ℝ) / t →
        ∀ η : ℚ, 0 < η → (η : ℝ) ≤ θ / 16 →
          (η : ℝ) ≤ (1 - θ / ((T.vertexCoverNum.toNat : ℝ) / t)) / 32 →
          ∃ N₁ : ℕ, ∀ N ≥ N₁,
            let v := T.vertexCoverNum.toNat
            let d := ⌊θ * N⌋₊
            let n₀ := ⌊(η : ℝ) * N⌋₊
            let ℓ := (d - 4 * n₀) / v
            let c := d - 4 * n₀ - v * ℓ
            let niso := N - 8 * n₀ - t * ℓ - 2 * c
            4 * n₀ ≤ d ∧ c < v ∧ (η : ℝ) * N / 2 ≤ n₀ ∧ 8 * n₀ + t * ℓ + 2 * c ≤ N ∧
              N = 8 * n₀ + t * ℓ + 2 * c + niso ∧ d = 4 * n₀ + v * ℓ + c ∧
              2 * max (max (2 * n₀ + 1) T.maxDegree) 2 ≤ d - 1 := by sorry

end MeanBudgetXC
