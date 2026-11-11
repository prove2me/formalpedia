-- Prove2me | Theorems.Thm_KXorTPCA_Reduction_corollary_12_1
-- name    : KXorTPCA.Reduction.corollary_12_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:24:44.603847+00:00
-- url     : https://prove2.me/theorems/16f16ccc-05c9-46bc-a748-a59478b753a4
-- title:
--   Corollary 12.1 — for even k′ ≤ min{k(1 − ρ), 2kρ}: k-Gauss_{ρ,η} → k′-Gauss_{1, 2η}; consequently CONJ_ρ ⇒ CONJ_1
-- statement:
--   1. Let $k\ge1$, $\rho\in(0,1]$ and $\eta\in\mathbb R$. If $k'>0$ is even and
--
--   $$k'\le\min\{k(1-\rho),\,2k\rho\},$$
--
--   then there is a polynomial-time average-case reduction (Definition C.6) for both detection and recovery from $k$-Gauss$_{\rho,\eta}(n)$ to $k'$-Gauss$_{\rho'=1,2\eta}(n')$, the Tensor PCA density, with $n'=n(1-o(1))$ ($n'_i\le n_i$ and $n'_i/n_i\to1$ along the sequences of Definition C.6).
--
--   2. Consequently, for every $\rho\in(0,1)$, $\mathrm{CONJ}_\rho\Rightarrow\mathrm{CONJ}_1$: for every detection error level $c\in[0,1]$, if for every $k\ge3$ and every $\eta>0$ no polynomial-time program solves detection with asymptotic error $c$ for $k$-XOR$_{\rho,\eta}(n)$, then the same holds at $\rho=1$; and likewise for each of exact, weak and strong recovery.
--
--   Differences from the source:
--   - reading: target "$k'$-Gauss$_{\rho'=1,2\eta}(n)$" → target dimensions $n'_i\le n_i$ with $n'_i/n_i\to1$, i.e. $n'=n(1-o(1))$; reason: the reduction (Lemma 8.1) changes the dimension to $n(1-o(1))$.
--   - reading: "$\mathrm{CONJ}_\rho\Rightarrow\mathrm{CONJ}_1$" → the implication for every detection error level $c\in[0,1]$ and for each recovery notion; reason: Believed Hardness 2.1 does not fix the error level or the recovery notion.
--   - reading: "$k'$ is even" → even $k'>0$; reason: tensor orders are positive.
--   - reading: "poly-time average-case reduction for both detection and recovery" → the mission's Definition C.6; reason: Definitions C.5/C.6 leave these choices open.
-- source:
--   G. Bresler, A. Harbuzova, Average-Case Reductions for k-XOR and Tensor PCA, arXiv:2601.19016 (copy sha256 6ec029a7…), p. 64 (PDF 67), Corollary 12.1, Eq. (43); pp. 5–6 (PDF 8–9), Believed Hardness 2.1, 2.2

import Mathlib
import Definitions.Def_KXorTPCA_Reduction_Reductions

open Filter Topology

namespace KXorTPCA.Reduction

theorem corollary_12_1 :
    (∀ k : ℕ, 1 ≤ k → ∀ ρ η : ℝ, 0 < ρ → ρ ≤ 1 →
      ∀ k' : ℕ, 0 < k' → Even k' →
        (k' : ℝ) ≤ min ((k : ℝ) * (1 - ρ)) (2 * (k : ℝ) * ρ) →
        AvgReduces (kModel (Choices.std .gauss) k) (ρ, η)
          (kModel (Choices.std .gauss) k') (1, 2 * η)
          (fun ns n's => (∀ i, n's i ≤ ns i) ∧
            Tendsto (fun i => (n's i : ℝ) / (ns i : ℝ)) atTop (𝓝 1))
          anySig) ∧
    (∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      (∀ c : ℝ, 0 ≤ c → c ≤ 1 → ConjDetAll c ρ → ConjDetAll c 1) ∧
      (∀ N : RecoveryNotion, ConjRecAll N ρ → ConjRecAll N 1)) := by sorry

end KXorTPCA.Reduction
