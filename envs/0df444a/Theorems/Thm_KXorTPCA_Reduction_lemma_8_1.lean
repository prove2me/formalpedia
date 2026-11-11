-- Prove2me | Theorems.Thm_KXorTPCA_Reduction_lemma_8_1
-- name    : KXorTPCA.Reduction.lemma_8_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:24:39.793409+00:00
-- url     : https://prove2.me/theorems/61912b68-703f-4ac0-8c53-265f51a0fd2c
-- title:
--   Lemma 8.1 — discrete equation-combination (resolution) reduction k-XOR_{ρ,η} → k′-XOR_{min(2kρ/k′,1), 2η}
-- statement:
--   Fix $k\ge1$, $\rho\in(-1,1]$, $\eta\in\mathbb R$ and an even order $k'\ge2$ with $k'\le k(1-\rho)$.
--
--   1. If $\rho\ge0$, there is a polynomial-time average-case reduction (Definition C.6) for both detection and recovery
--
--   $$k\text{-XOR}_{\rho,\eta}(n)\ \longrightarrow\ k'\text{-XOR}_{\rho',2\eta}(n'),\qquad \rho'=\min\Big\{\tfrac{2k}{k'}\rho,\,1\Big\}.$$
--
--   2. If $\rho<0$ and $k'>2k|\rho|$, then for every constant $\delta\in(0,1]$ there is one from $k$-XOR$(n,m=n^{k(1+\rho)/2},\delta)$ to $k'$-XOR$(n',m'=\tilde\Theta(n'^{k'(1+\rho')/2}),\delta^2)$ with $\rho'=\frac{2k}{k'}\rho$; formally, from the family $(a,b)\mapsto k$-XOR$(n,n^{k(1+a)/2},\delta n^{-b/2})$ at $(\rho,0)$ to the family $(a,b)\mapsto k'$-XOR$(n,n^{k'(1+a)/2},\delta^2 n^{-b/2})$ at $(\rho',0)$.
--
--   In both cases the reduction maps the secret $x\in\{\pm1\}^n$ to $x'=x[1:n']$, the first $n'$ coordinates, with $n'_i\le n_i$ and $n'_i/n_i\to1$ ($n'=n(1-o(1))$).
--
--   Multiplying two noisy equations gives a noisy equation on the symmetric difference of their supports with squared signal; the lemma makes this a distributionally correct reduction.
--
--   Differences from the source:
--   - reading: case $\rho<0$, "from $k$-XOR$(n,m=n^{k(1+\rho)/2},\delta)$ to $k'$-XOR$(n',m'=\tilde\Theta(n'^{k'(1+\rho')/2}),\delta^2)$" → for every constant $\delta\in(0,1]$, between the families above at $(\rho,0)$ and $(\rho',0)$; reason: Definition C.6 needs a parametrized family; the $\tilde\Theta$ in $m'$ and $\delta$ are absorbed by its parameter sequences.
--   - reading: $n'=n(1-o(1))$ → $n'_i\le n_i$ and $n'_i/n_i\to1$; reason: literal meaning along the sequence.
--   - reading: "even integer $k'$" → even $k'>0$; reason: tensor orders are positive.
--   - reading: "average-case reduction (Def. C.6) for both detection and recovery" → the mission's Definition C.6; reason: Definitions C.5/C.6 leave these choices open.
--   - reading: $m=n^{k(1+\rho)/2}$ samples → $\lfloor m\rfloor$; reason: $m$ is real.
-- source:
--   G. Bresler, A. Harbuzova, Average-Case Reductions for k-XOR and Tensor PCA, arXiv:2601.19016 (copy sha256 6ec029a7…), pp. 29–30 (PDF 32–33), Lemma 8.1

import Mathlib
import Definitions.Def_KXorTPCA_Reduction_Reductions

open Filter Topology

namespace KXorTPCA.Reduction

theorem lemma_8_1 :
    ∀ k : ℕ, 1 ≤ k → ∀ ρ η : ℝ, -1 < ρ → ρ ≤ 1 →
    ∀ k' : ℕ, 0 < k' → Even k' → (k' : ℝ) ≤ (k : ℝ) * (1 - ρ) →
      (0 ≤ ρ →
        AvgReduces (kModel (Choices.std .xor) k) (ρ, η)
          (kModel (Choices.std .xor) k') (min (2 * (k : ℝ) / k' * ρ) 1, 2 * η)
          (fun ns n's => (∀ i, n's i ≤ ns i) ∧
            Tendsto (fun i => (n's i : ℝ) / (ns i : ℝ)) atTop (𝓝 1))
          prefixSig) ∧
      (ρ < 0 → 2 * (k : ℝ) * |ρ| < k' → ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        AvgReduces
          (fun a b n => modelTask (Choices.std .xor) k n
            ((n : ℝ) ^ ((k : ℝ) * (1 + a) / 2)) (δ * (n : ℝ) ^ (-b / 2))) (ρ, 0)
          (fun a b n => modelTask (Choices.std .xor) k' n
            ((n : ℝ) ^ ((k' : ℝ) * (1 + a) / 2)) (δ ^ 2 * (n : ℝ) ^ (-b / 2)))
          (2 * (k : ℝ) / k' * ρ, 0)
          (fun ns n's => (∀ i, n's i ≤ ns i) ∧
            Tendsto (fun i => (n's i : ℝ) / (ns i : ℝ)) atTop (𝓝 1))
          prefixSig) := by sorry

end KXorTPCA.Reduction
