-- Prove2me | Theorems.Thm_ImpuritySim_lemma_B_1
-- name    : ImpuritySim.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:36:39.983728+00:00
-- url     : https://prove2.me/theorems/348c85d6-61e6-46af-82e0-12b4680dcbc1
-- title:
--   Lemma B.1 — counting bound $|\{x:D(x)\le T\}|\le\exp(8T+3\chi)$
-- statement:
--   Let $H$ be in the form (3.15) on $n$ modes and let the weights satisfy (4.2) and $h_d\ge\min\{d-1,\tau\}$ for every $d\ge1$, where $\tau\ge\max\{1,\frac18\log n\}$. Then for every real $T$,
--   $$|\{x\in\{0,1\}^n:D(x)\le T\}|\le\exp(8T+3\chi),\qquad(B.1)$$
--   where $\chi$ (3.18) is the enlarged-impurity size plus the maximal number of residual-bath modes at one depth, summed over all bands.
--
--   This turns the exponential-moment threshold of Theorem 4.1 into a bound on the dimension of the compressed space.
--
--   **Formalization Note** $\log$ is the natural logarithm and $n$ the number of modes; the standing conditions (4.2), under which $D$ is defined, are hypotheses.
--
--   Differences from the source:
--   - generalization: an impurity Hamiltonian in the bandwise hybridization form (3.15), built from (1.1) by App. A and §3 → any BandwiseForm: any data on n modes with the properties (3.15)–(3.18) and Lemma 3.1 record (bath set, bands ≤ L, depths ≥ 1, shell sizes ≤ 2m, impurity size ≤ m + 2m(L+1), E Hermitian, band-diagonal and depth-tridiagonal with ω_ℓ I ≤ E_ℓ ≤ 2ω_ℓ I, orthonormal u_ℓs in the depth-1 shell, ‖G_ℓs‖ ≤ 2ω_ℓ, K even on the enlarged impurity); reason: every form produced by the paper's construction has these properties, so the statement specializes to the paper's; the proofs use only these properties
-- source:
--   Jiang–Ju–Parekh–Rayudu–Zhao, Polynomial-time classical and quantum simulation of quantum impurity models, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), Lemma B.1, Eq. (B.1), p.54; (3.18), p.18; (4.2)–(4.3), p.20

import Mathlib
import Definitions.Def_ImpuritySim_Occupation

open Matrix

namespace ImpuritySim

/-- **Lemma B.1 (Counting bound)**, p.54, of J. Jiang, N. Ju, O. Parekh, C. Rayudu, A. Zhao,
*Polynomial-time classical and quantum simulation of quantum impurity models*, arXiv:2610.02167
(held version, sha256 88d2a4e6…f0fff9b2), Eq. (B.1), with (3.18) and (4.3).

Assume that `h_d ≥ min{d − 1, τ}` for every `d ≥ 1`, where `τ ≥ max{1, (1/8) log n}`. Then for
every real `T`, `|{x : D(x) ≤ T}| ≤ exp(8T + 3χ)`, where `χ` (3.18) is the enlarged-impurity size
plus the maximal number of residual-bath modes at one depth, summed over all bands.

**Formalization Note.** `n` is the number of modes, `log` the natural logarithm; the weights also
satisfy the standing conditions (4.2) of §4.1, under which `D` is defined; `x` ranges over all of
`{0,1}^n` (`thresholdSet`). -/
theorem lemma_B_1 {n : ℕ} (F : BandwiseForm n) (τ : ℝ) (hτ : max 1 (Real.log n / 8) ≤ τ)
    (h : ℕ → ℝ) (hh : ValidWeights h) (hcut : ∀ d : ℕ, 1 ≤ d → min ((d : ℝ) - 1) τ ≤ h d) (T : ℝ) :
    ((F.thresholdSet h T).card : ℝ) ≤ Real.exp (8 * T + 3 * F.chi) := by sorry

end ImpuritySim
