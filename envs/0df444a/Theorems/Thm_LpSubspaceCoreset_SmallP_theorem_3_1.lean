-- Prove2me | Theorems.Thm_LpSubspaceCoreset_SmallP_theorem_3_1
-- name    : LpSubspaceCoreset.SmallP.theorem_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:48:20.045698+00:00
-- url     : https://prove2.me/theorems/77a480e2-fbce-4880-9cb0-89b588460d2e
-- title:
--   Theorem 3.1 — low-rank-split coreset
-- statement:
--   Fix $1\le p<2$, $\Gamma\ge1$ and the constant $c>0$ implicit in (3.2). There is $C=C_{p,\Gamma,c}$ such that the following holds. Let $k\ge1$ and $A=B+E\in\mathbb R^{n\times d}$ with $r=\operatorname{rank}B\ge1$ and $R=\sum_i\|e_i\|_2^p\le\Gamma\,\mathrm{OPT}_A$ (3.1); put $D=k+r$, let $w_i$ be the Lewis weights of the rows $b_i$ ($w_i=0$ when $b_i=0$), and $\rho_i=\|e_i\|_2^p/R$ when $R>0$, $\rho_i=0$ when $R=0$. Let $q$ be any probability distribution with
--   $$q_i\ge c\Big(\frac{w_i}D+\rho_i\Big)\qquad(i\in[n]).\qquad(3.2)$$
--   Fix $0<\varepsilon,\eta<1/2$ and let $m\ge C\,D\varepsilon^{-2}\eta^{-2}\big(\log(n+D+\varepsilon^{-1}+\eta^{-1})\big)^{C}$. If $S$ is formed from $m$ independent draws from $q$ reweighted as in Definition 2.3, then with probability at least $1-\eta$,
--   $$\mathrm{cost}_{SA}(F)=(1\pm\varepsilon)\,\mathrm{cost}_A(F)\quad\text{simultaneously for every }F\in\mathcal F_k .$$
--   This is the paper's core sampling theorem; Proposition 4.1 implements it in input-sparsity time.
--
--   Differences from the source:
--   - reading: q_i ≳_{p,Γ} w_i/D + ρ_i → ∀ c > 0, q_i ≥ c (w_i/D + ρ_i), with C chosen after c; reason: the implied constant of ≳ is a fixed constant and the Õ constant may depend on it
--   - reading: m = Õ_{p,Γ}(D ε^{-2} η^{-2}), polylog in n + D + ε^{-1} + η^{-1} → every m ≥ C·D·ε^{-2}·η^{-2}·(log(n + D + 1/ε + 1/η))^C; reason: an explicit polylogarithmic factor; every sample size above the bound works
--   - encoding: with probability at least 1 − η over the draws → sampleProb: Σ over samples I ∈ [n]^m of Π_s q_{I_s} times the indicator; reason: the product law of the i.i.d. draws, a finite sum
-- source:
--   Lin, Mirrokni, Woodruff, Nearly Optimal Strong Coresets for ℓp Subspace Approximation, arXiv:2608.26047 (held PDF of 2026-11-03, sha256 4c61606e…), p. 16, Theorem 3.1

import Mathlib
import Definitions.Def_LpSubspaceCoreset_SmallP_Cost
import Definitions.Def_LpSubspaceCoreset_SmallP_Sampling
import Definitions.Def_LpSubspaceCoreset_SmallP_Lewis

namespace LpSubspaceCoreset.SmallP

/-- **Theorem 3.1** (Low-rank-split coreset), p. 16.

Fix `1 ≤ p < 2`, `Γ ≥ 1` and the constant `c > 0` of (3.2); there is `C = C_{p,Γ,c}` such that the
following holds. Let `k ≥ 1` and `A = B + E` with `r = rank(B) ≥ 1` and
`R = Σ_i ‖e_i‖₂^p ≤ Γ·OPT_A` (3.1); `D = k + r`; `w_i` the Lewis weights of the rows `b_i`
(`w_i = 0` when `b_i = 0`); `ρ_i = ‖e_i‖₂^p/R` if `R > 0` and `ρ_i = 0` if `R = 0`. Let `q` be any
probability distribution with `q_i ≥ c (w_i/D + ρ_i)` for every `i` (3.2). Let `0 < ε, η < 1/2`
and let `m` be any sample size with `m ≥ C D ε^{−2} η^{−2} (log(n + D + 1/ε + 1/η))^C`. If `S` is
formed from `m` independent draws from `q` as in Definition 2.3, then with probability at least
`1 − η`, `S` is a `(1 ± ε)` strong row coreset of `A` (all `F` with `dim F ≤ k` at once). -/
theorem theorem_3_1 :
    ∀ p : ℝ, 1 ≤ p → p < 2 → ∀ Γ : ℝ, 1 ≤ Γ → ∀ c : ℝ, 0 < c →
    ∃ C : ℝ, 0 < C ∧
    ∀ (n d k : ℕ), 1 ≤ k →
    ∀ (A B E : Matrix (Fin n) (Fin d) ℝ), A = B + E → 1 ≤ B.rank →
      ∑ i, norm2 (E i) ^ p ≤ Γ * OPT p k A →
    ∀ w : Fin n → ℝ, IsLewisWeights p B w →
      let R : ℝ := ∑ i, norm2 (E i) ^ p
      let D : ℝ := (k : ℝ) + B.rank
      let ρ : Fin n → ℝ := fun i => if 0 < R then norm2 (E i) ^ p / R else 0
    ∀ q : Fin n → ℝ, IsProbVec q → (∀ i, c * (w i / D + ρ i) ≤ q i) →
    ∀ ε η : ℝ, 0 < ε → ε < 1 / 2 → 0 < η → η < 1 / 2 →
    ∀ m : ℕ, C * D / ε ^ 2 / η ^ 2 * (Real.log (n + D + 1 / ε + 1 / η)) ^ C ≤ m →
      1 - η ≤ sampleProb q m (fun I => IsStrongCoreset p k ε A (samplingMatrix p q I)) := by sorry

end LpSubspaceCoreset.SmallP
