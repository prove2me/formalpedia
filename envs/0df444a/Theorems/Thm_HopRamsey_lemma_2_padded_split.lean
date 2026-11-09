-- Prove2me | Theorems.Thm_HopRamsey_lemma_2_padded_split
-- name    : HopRamsey.lemma_2_padded_split
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:45:11.314195+00:00
-- url     : https://prove2.me/theorems/03f63c8b-93c7-4730-810b-363c6904d7d8
-- title:
--   Padded-split bound: $\Pr[\rho_u+1\le R\le\rho_v-2]\le p\,\chi\cdot\Pr[R\ge s]$
-- statement:
--   Let $R$ be geometric with parameter $p\in(0,1]$, let $\rho_u\le\rho_v$ be integers, $s=\max\{0,\rho_u-1\}$, and let $\chi\ge0$ be real with $\rho_v\le\rho_u+\lceil\chi\rceil$. Then
--
--   $$
--   \Pr[\rho_u+1\le R\le\rho_v-2]\le p\cdot\max\{0,\rho_v-\rho_u-2\}\cdot\Pr[R\ge s],
--   $$
--
--   and $p\cdot\max\{0,\rho_v-\rho_u-2\}\le p\cdot\max\{0,\lceil\chi\rceil-2\}\le p\,\chi$.
--
--   In the proof of Lemma 2 this bounds the probability that a ball separates $u$ from $v$ while both stay padded by $p_\ell\,d^{(h)}_G(u,v)/q_\ell$, relative to the probability that the ball reaches them.
--
--   Differences from the source:
--   - generalization: R the radius of a carved ball, geometric with parameter p_ℓ; χ_ℓ = d^{(h)}_G(u,v)/q_ℓ → R geometric with any p ∈ (0,1]; any real χ ≥ 0 with ρ_v ≤ ρ_u + ⌈χ⌉; reason: the bound uses only these properties, all established just before it on p.23
--   - encoding: the conditional probability given R ≥ s → the product form Pr[split] ≤ p·max{0,ρ_v−ρ_u−2}·Pr[R ≥ s]; reason: equivalent to the conditional bound when Pr[R ≥ s] > 0, and the event is contained in {R ≥ s} when it is 0
-- source:
--   Filtser, Zuzic, Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with Logarithmic Expected Distortion, STOC 2027 submission (manuscript sha256 1ee73385…), proof of Lemma 2, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_HopRamsey_truncGeom

open scoped ENNReal

namespace HopRamsey

/-- Filtser, Zuzic, *Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with
Logarithmic Expected Distortion*, STOC 2027 submission (manuscript sha256 1ee73385…),
Padded-split bound, proof of Lemma 2, p.23 (PDF p.25): "Set s = max{0,ρ_u−1}. Conditional on a hit
R ≥ s, each possible radius has probability at most p_ℓ, by memorylessness. A padded split requires
ρ_u+1 ≤ R ≤ ρ_v−2, so its conditional probability is at most
p_ℓ · max{0,ρ_v−ρ_u−2} ≤ p_ℓ · max{0,⌈χ_ℓ⌉−2} ≤ p_ℓ · χ_ℓ."

**Formalization Note.** `R` has the geometric law with parameter `p ∈ (0, 1]`; `ρ_u ≤ ρ_v` are
integers and `χ ≥ 0` is real with `ρ_v ≤ ρ_u + ⌈χ⌉` (shown just before, p.23). The conditional
bound is stated in product form, `Pr[split] ≤ p·max{0, ρ_v−ρ_u−2}·Pr[R ≥ s]`, followed by the two
arithmetic steps. -/
theorem lemma_2_padded_split (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (ρu ρv : ℤ) (hρ : ρu ≤ ρv)
    (χ : ℝ) (hχ : 0 ≤ χ) (hχρ : ρv ≤ ρu + ⌈χ⌉) :
    (geomLaw p).toOuterMeasure {R : ℕ | ρu + 1 ≤ (R : ℤ) ∧ (R : ℤ) ≤ ρv - 2} ≤
        ENNReal.ofReal (p * max 0 ((ρv - ρu - 2 : ℤ) : ℝ)) *
          (geomLaw p).toOuterMeasure {R : ℕ | max 0 (ρu - 1) ≤ (R : ℤ)} ∧
      p * max 0 ((ρv - ρu - 2 : ℤ) : ℝ) ≤ p * max 0 (((⌈χ⌉ : ℤ) : ℝ) - 2) ∧
      p * max 0 (((⌈χ⌉ : ℤ) : ℝ) - 2) ≤ p * χ := by sorry

end HopRamsey
