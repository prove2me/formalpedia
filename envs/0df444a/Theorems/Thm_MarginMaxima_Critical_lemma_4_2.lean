-- Prove2me | Theorems.Thm_MarginMaxima_Critical_lemma_4_2
-- name    : MarginMaxima.Critical.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:02:50.342382+00:00
-- url     : https://prove2.me/theorems/c5b5eef2-b0e4-4d07-9d0e-9b2c086d2b80
-- title:
--   Lemma 4.2 — random labels on an $(M,j)$-regular block system: with probability $\ge 11/16$ the sample is good
-- statement:
--   Let $C$ carry a block system, $n=|C|$, $M_0\le M$ an integer, $p=M_0/M$, $\pi_0=\Pr[\mathrm{Bin}(M-1,p)=M_0-1]$, $\rho\in(0,1)$, $\delta\in(0,1/2]$, $c_\rho=\ln(32/\rho)$, $np\ge64$, $\delta np\ge 8\ln16$, and let the system be $(M,j)$-regular with $j=\lceil c_\rho\delta^{-(M_0-1)}/\pi_0\rceil$. Let $X$ and $S$ be independent random subsets of $C$ with rates $p$ and $\delta$. With probability at least $11/16$, simultaneously
--   $$|X|\in[np/2,2np],\quad |X\cap S|\ge\delta np/2,\quad |U|\le\rho\delta np/2,\quad H\le 8(c_\rho+1)\delta np/M_0.$$
--
--   Differences from the source:
--   - encoding: with probability at least 11/16 over independent random X (rate p) and S (rate δ) → 11/16 ≤ sampleProb p δ E, the sum over pairs of subsets of the product Bernoulli point masses of the event E; reason: the law of (X, S) on the finite space of pairs of subsets; every event is measurable
--   - encoding: a block system: Hilbert space ℒ ⊥ h₀, documents ξ_y + κh₀, heads ℓ_B − κh₀ → BlockSystem L C β g s κ with L a complete real inner product space, blocks indexed by β, and scores ⟨ℓ, ξ_y⟩ − κ²; reason: ⟨ℓ − κh₀, ξ + κh₀⟩ = ⟨ℓ, ξ⟩ − κ² since ℓ, ξ ⊥ h₀ and ∥h₀∥ = 1; the same systems
--   - encoding: n = |C|, M₀ ≤ M an integer, p = M₀/M → Fintype.card C, M M0 : ℕ with M0 ≤ M, p written (M0 : ℝ)/M; reason: the §4 setting (p. 8)
--   - encoding: j = ⌈c_ρ δ^{−(M₀−1)}/π₀⌉ → ⌈Real.log (32/ρ) * (δ ^ (M0 − 1))⁻¹ / pi0 M M0 p⌉₊; reason: Nat.ceil; M0 ≥ 1 follows from np ≥ 64
-- source:
--   Tianlang Chen, The Margin Complexity of Maxima of Linear Functionals, STOC 2027 submission (manuscript sha256 dbfb896a…3901), p. 8, Lemma 4.2

import Mathlib
import Definitions.Def_MarginMaxima_Critical_BlockSystem

namespace MarginMaxima.Critical

theorem lemma_4_2 {L : Type} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [CompleteSpace L]
    {C β : Type} [Fintype C] [DecidableEq C] [Fintype β] {g s κ : ℝ}
    (S : BlockSystem L C β g s κ) (M M0 : ℕ) (hM0 : M0 ≤ M) (ρ δ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hnp : 64 ≤ (Fintype.card C : ℝ) * ((M0 : ℝ) / M))
    (hδnp : 8 * Real.log 16 ≤ δ * (Fintype.card C : ℝ) * ((M0 : ℝ) / M))
    (hreg : S.IsRegular M
      ⌈Real.log (32 / ρ) * (δ ^ (M0 - 1))⁻¹ / pi0 M M0 ((M0 : ℝ) / M)⌉₊) :
    11 / 16 ≤ sampleProb ((M0 : ℝ) / M) δ fun X Sm =>
      ((Fintype.card C : ℝ) * ((M0 : ℝ) / M) / 2 ≤ X.card ∧
          (X.card : ℝ) ≤ 2 * ((Fintype.card C : ℝ) * ((M0 : ℝ) / M))) ∧
        δ * ((Fintype.card C : ℝ) * ((M0 : ℝ) / M)) / 2 ≤ ((X ∩ Sm).card : ℝ) ∧
        ((S.uncovered M0 X Sm).card : ℝ) ≤ ρ * δ * ((Fintype.card C : ℝ) * ((M0 : ℝ) / M)) / 2 ∧
        (S.numChosen M0 X Sm : ℝ) ≤
          8 * (Real.log (32 / ρ) + 1) * δ * ((Fintype.card C : ℝ) * ((M0 : ℝ) / M)) / M0 := by sorry

end MarginMaxima.Critical
