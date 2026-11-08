-- Prove2me | Theorems.Thm_MantriCVQ_theorem_6_9
-- name    : MantriCVQ.theorem_6_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:09:35.435407+00:00
-- url     : https://prove2.me/theorems/6c93ee0b-3c57-4cf2-a3cf-079806b4c9df
-- title:
--   Theorem 6.9 — tail bound for certificate complexity, Eq. (6.3)
-- statement:
--   Let $\rho$ be a product of $K$ independent random projections, one per block, each fixing every leaf except one free leaf, sampled independently of the free values. Suppose that for every integer $1\le r\le W$ and every DNF of width at most $W$ on the leaves of $r$ of the blocks, the DNF accepts $X$ and is sensitive at $X$ to every one of the $r$ blocks with probability at most $2^{-\gamma r}$, uniformly over the free values. Then for every CNF $\Psi$ of width at most $W$ on the leaves of the blocks, every $z\in\mathbb F_2^K$ and every integer $q\ge0$, the projected CNF $H_\rho=\Psi\circ\rho$ satisfies
--   $$\Pr_\rho\bigl[H_\rho(z)=1\text{ and }\mathrm C_1(H_\rho,z)>q\bigr]\le\sum_{\Lambda=\lceil(q+1)/(2W+1)\rceil}^{K}2^{-(\gamma-2\log K)\Lambda}.$$
--   An empty sum is zero. The hypothesis does not involve the code family or the recursion.
--
--   Differences from the source:
--   - encoding: a projection of K blocks (§6.3) → a finite leaf type and a law on (free leaf, leaf values) per block, with the product law; reason: this is §6.3's own definition
--   - encoding: a DNF on the leaves of r of the blocks, uniformly over the free values → a DNF whose literals all lie in a set R of r blocks, with free values given on all K blocks; reason: the DNF does not read the other blocks, so their values and laws do not matter
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Theorem 6.9, Eq. (6.3), p. 29 (PDF p. 31)

import Mathlib
import Definitions.Def_MantriCVQ_C1
import Definitions.Def_MantriCVQ_CNF
import Definitions.Def_MantriCVQ_ProductProjection
import Definitions.Def_MantriCVQ_listWidth
import Definitions.Def_SamplingAC0_DNF

open SamplingAC0

namespace MantriCVQ

/-- **Theorem 6.9** (Mantri, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Theorem 6.9, Eq. (6.3), p. 29 (PDF p. 31)): let `ρ` be a projection of `K` blocks.
Suppose that for every `1 ≤ r ≤ W` and every DNF of width at most `W` on the leaves of `r` of the blocks, the
DNF accepts `X` and is sensitive at `X` to every one of the `r` blocks with probability at most `2^{-γr}`,
uniformly over the free values. Then for every CNF `Ψ` of width at most `W`, every `z` and every `q ≥ 0`,
`Pr_ρ[H_ρ(z) = 1 and C₁(H_ρ, z) > q] ≤ ∑_{Λ=⌈(q+1)/(2W+1)⌉}^{K} 2^{-(γ - 2 log K)Λ}`, where `H_ρ = Ψ ∘ ρ`.

**Formalization Note** A DNF "on the leaves of `r` of the blocks" is a DNF all of whose variables lie in a
set `R` of `r` blocks; it does not read the free values of the other blocks. `γ` is real and `log` is
`log₂`. An empty sum is zero (`Finset.Icc`). -/
theorem theorem_6_9 {K W : ℕ} {Λ : Fin K → Type} [∀ i, Fintype (Λ i)] [∀ i, DecidableEq (Λ i)]
    (π : ∀ i, PMF (Λ i × (Λ i → Bool))) (γ : ℝ)
    (hsens : ∀ r : ℕ, 1 ≤ r → r ≤ W → ∀ R : Finset (Fin K), R.card = r →
      ∀ Φ : DNF (Σ i, Λ i), listWidth Φ ≤ W → (∀ T ∈ Φ, ∀ l ∈ T, l.1.1 ∈ R) →
      ∀ v : Fin K → Bool,
        prodProb π (fun ω => DNF.eval Φ (prodInput ω v) = true ∧
            ∀ i ∈ R, DNF.eval Φ (prodInput ω (Function.update v i (!v i))) = false) ≤
          (2 : ℝ) ^ (-(γ * r)))
    (Ψ : CNF (Σ i, Λ i)) (hΨ : listWidth Ψ ≤ W) (z : Fin K → Bool) (q : ℕ) :
    prodProb π (fun ω => CNF.eval Ψ (prodInput ω z) = true ∧
        q < C1 (fun z' => CNF.eval Ψ (prodInput ω z')) z) ≤
      ∑ L ∈ Finset.Icc ⌈((q : ℝ) + 1) / (2 * W + 1)⌉₊ K,
        (2 : ℝ) ^ (-((γ - 2 * Real.logb 2 K) * L)) := by sorry

end MantriCVQ
