-- Prove2me | Theorems.Thm_KXorTPCA_Reduction_lemma_6_4
-- name    : KXorTPCA.Reduction.lemma_6_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:24:38.595126+00:00
-- url     : https://prove2.me/theorems/5492c0d0-a0f0-4dc4-80fd-3572610708a2
-- title:
--   Lemma 6.4 — reducing order k to k/a on FULL models: η → η/a, n′ = n^a, x′ = x^{⊗a} ⊙ y
-- statement:
--   Fix a noise model, a sample count rule and a sampling rule, $k\ge1$, $\rho\in[0,1]$, $\eta\in\mathbb R$ and $a\ge1$ with $a\mid k$. There is a polynomial-time average-case reduction (Definition C.6) for both detection and recovery
--
--   $$k\text{-model}^{\star,\mathrm{FULL}}_{\rho,\eta}(n)\ \longrightarrow\ (k/a)\text{-model}^{\star,\mathrm{FULL}}_{\rho,\eta/a}(n'),\qquad n'=n^a,$$
--
--   which maps the secret $x\in\{\pm1\}^n$ to $x'=x^{\otimes a}\odot y$: for a bijection $N:[n']\to[n]^a$, $x'_i=y_i\prod_{j=1}^a x_{N(i)_j}$, where $y\in\{\pm1\}^{n'}$ is uniform, drawn by the reduction (and so known to its recovery map).
--
--   Differences from the source:
--   - reading: "for a known $y\sim\mathrm{Unif}[\{\pm1\}^{n'}]$" → $y$ a function of the reduction's tapes taking each value with probability $2^{-n'}$; the recovery map sees those tapes; reason: "known" means available to the recovery step.
--   - reading: "Let $N:[n]^a\to[n^a]$ be any bijection" (Alg. B.4) → some bijection; reason: the reduction chooses it.
--   - reading: "$k,n\in\mathbb Z_+$" → $k\ge1$ (and every dimension along the sequences); reason: Definition C.6 quantifies the dimensions.
--   - reading: "average-case reduction for both detection and recovery" → the mission's Definition C.6, with $n'_i=n_i^a$; reason: Definitions C.5/C.6 leave these choices open.
-- source:
--   G. Bresler, A. Harbuzova, Average-Case Reductions for k-XOR and Tensor PCA, arXiv:2601.19016 (copy sha256 6ec029a7…), p. 26 (PDF 29), Lemma 6.4; p. 93 (PDF 96), Algorithm B.4

import Mathlib
import Definitions.Def_KXorTPCA_Reduction_Reductions

open MeasureTheory
open scoped ENNReal

namespace KXorTPCA.Reduction

theorem lemma_6_4 :
    ∀ (nz : Noise) (cnt : Count) (smp : Sampling) (k : ℕ), 1 ≤ k →
    ∀ ρ η : ℝ, 0 ≤ ρ → ρ ≤ 1 → ∀ a : ℕ, 0 < a → a ∣ k →
      AvgReduces (kModel ⟨nz, cnt, .full, smp⟩ k) (ρ, η)
        (kModel ⟨nz, cnt, .full, smp⟩ (k / a)) (ρ, η / a)
        (fun ns n's => ∀ i, n's i = ns i ^ a)
        (fun n n' σ => ∃ (e : Fin n' → (Fin a → Fin n)) (y : Tapes → Signal n'),
          Function.Bijective e ∧
          (∀ v : Signal n', tapeLaw {ω | y ω = v} = ((2 : ℝ≥0∞) ^ n')⁻¹) ∧
          ∀ (x : Signal n) (ω : Tapes) (i : Fin n'), σ x ω i = (∏ j, x (e i j)) * y ω i) := by sorry

end KXorTPCA.Reduction
