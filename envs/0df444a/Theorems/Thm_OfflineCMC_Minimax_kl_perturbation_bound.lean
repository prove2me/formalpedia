-- Prove2me | Theorems.Thm_OfflineCMC_Minimax_kl_perturbation_bound
-- name    : OfflineCMC.Minimax.kl_perturbation_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:38:54.706095+00:00
-- url     : https://prove2.me/theorems/f6b47ea4-e115-4c7c-a21f-52d1d6290e93
-- title:
--   G.3 Part 1, p. 52 (corrected: bracket in the intermediate bound) — D_σ = KL(η(σ) ‖ b) ≤ 256ε²/(1 − p★) ≤ 512ε²
-- statement:
--   Let $d\ge2$ be even, $0<p_\star<1/(d+1)$ and $0<\varepsilon<1/32$. Let $b=((1-p_\star)/d,\dots,(1-p_\star)/d,p_\star)$ and let $\eta(\sigma)$ be its perturbation by the sign vector $\sigma\in\{-1,1\}^{d/2}$ (the last row of $M_\sigma$ in (G.19)). Then the Kullback–Leibler divergence $D_\sigma=\sum_t\eta(\sigma)_t\log(\eta(\sigma)_t/b_t)$ satisfies
--   $$
--   D_\sigma\le\frac{256\,\varepsilon^2}{1-p_\star}\le512\,\varepsilon^2 .
--   $$
--
--   This bounds the information one visit to the special state carries about $\sigma$. Combined with the chain rule (G.22), it bounds the divergence between the path laws of the hard family.
--
--   Differences from the source:
--   - correction: the intermediate display $D_\sigma\le\frac12(A+B)\frac BA-(A-B)\frac BA=\frac{B^2}A$ → not stated; only $D_\sigma\le B^2/A=256\varepsilon^2/(1-p_\star)\le512\varepsilon^2$ is asserted; reason: as printed the middle expression is not $B^2/A$ (a lost bracket: $\frac12\big((A+B)\frac BA-(A-B)\frac BA\big)=B^2/A$), while the two endpoints are correct
--   - generalization: $d>2$ even (Part 1's hypothesis) → $d\ge2$ even; reason: covers $d=2$ as well
-- source:
--   Banerjee, Honnappa & Rao, Offline Estimation of Controlled Markov Chains: Minimaxity and Sample Complexity, arXiv:2211.07092v5, p. 52, App. G.3 Part 1 (D_σ)

import Mathlib
import Definitions.Def_OfflineCMC_Minimax_CMC
import Definitions.Def_OfflineCMC_Minimax_HardFamily

namespace OfflineCMC.Minimax

theorem kl_perturbation_bound (d : ℕ) (hd : Even d) (hd0 : 0 < d) (p ε : ℝ) (hp : 0 < p)
    (hpd : p < 1 / ((d : ℝ) + 1)) (hε : 0 < ε) (hε' : ε < 1 / 32) (σ : Fin (d / 2) → ℤˣ) :
    klDivFin (etaRow d p ε σ) (baseRow d p) ≤ 256 * ε ^ 2 / (1 - p) ∧
      256 * ε ^ 2 / (1 - p) ≤ 512 * ε ^ 2 := by sorry

end OfflineCMC.Minimax
