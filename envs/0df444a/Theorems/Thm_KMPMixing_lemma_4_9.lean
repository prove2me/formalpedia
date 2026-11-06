-- Prove2me | Theorems.Thm_KMPMixing_lemma_4_9
-- name    : KMPMixing.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:10:32.787202+00:00
-- url     : https://prove2.me/theorems/85fc8850-05ed-4d1d-bb26-801013792340
-- title:
--   Lemma 4.9 — couplings of two uniform splits
-- statement:
--   Let $B,D\in\mathbb N$.
--
--   1. Let $\xi\sim\mathrm{Unif}[0,1)$, $Z=\lfloor(B+1)\xi\rfloor$ and $\widetilde Z=\lfloor(D+1)\xi\rfloor$. Then $Z\sim\mathrm{Unif}\{0,\dots,B\}$, $\widetilde Z\sim\mathrm{Unif}\{0,\dots,D\}$, and
--   $$
--   |Z-\widetilde Z|+|(B-Z)-(D-\widetilde Z)|=|B-D|.\tag{15}
--   $$
--   2. Let $A,C\in\mathbb N$ and $h,L\ge0$ with $|A-C|\le h$, $|B-D|\le h$ and $B,D\ge L$. Then there is a coupling of $Z\sim\mathrm{Unif}\{0,\dots,B\}$ and $\widetilde Z\sim\mathrm{Unif}\{0,\dots,D\}$ with
--   $$
--   \Pr[A+Z\ne C+\widetilde Z]\le\frac{3h}{L+1}.
--   $$
--
--   These are the one-edge couplings from which the exact coupling of Lemma 4.10 is assembled.
--
--   Differences from the source:
--   - encoding: $Z\sim\mathrm{Unif}\{0,\dots,B\}$ under $\xi\sim\mathrm{Unif}[0,1)$ → for each $z\le B$, the Lebesgue measure of $\{\xi\in[0,1):\lfloor(B+1)\xi\rfloor=z\}$ is $1/(B+1)$ (likewise for $D$); (15) for every $\xi\in[0,1)$, in $\mathbb Z$; reason: the same law, and (15) is a pointwise identity
--   - encoding: a coupling → a nonnegative function on $\{0,\dots,B\}\times\{0,\dots,D\}$ with uniform marginals; reason: the definition of a coupling of two laws on finite sets
-- source:
--   Chen et al., arXiv:2609.38044, Lemma 4.9, pp.24–25 (PDF pp.26–27)

import Mathlib
open MeasureTheory

namespace KMPMixing

/-- **Lemma 4.9** (arXiv:2609.38044, pp.24–25 (PDF pp.26–27)). Let `B, D ∈ ℕ`.

(i) Sample `ξ ∼ Unif[0, 1)` and set `Z = ⌊(B + 1)ξ⌋`, `Z̃ = ⌊(D + 1)ξ⌋`. Then
`Z ∼ Unif{0, …, B}`, `Z̃ ∼ Unif{0, …, D}`, and
`|Z − Z̃| + |(B − Z) − (D − Z̃)| = |B − D|` (Eq. (15)).

(ii) Let `A, C ∈ ℕ` and `h, L ≥ 0` satisfy `|A − C| ≤ h`, `|B − D| ≤ h` and `B, D ≥ L`. There is a
coupling of `Z ∼ Unif{0, …, B}` and `Z̃ ∼ Unif{0, …, D}` with `Pr[A + Z ≠ C + Z̃] ≤ 3h/(L + 1)`.

**Formalization Note** `Unif[0, 1)` is Lebesgue measure on `[0, 1)`; "`Z ∼ Unif{0,…,B}`" is
stated as: for each `z ≤ B` the set `{ξ ∈ [0,1) : ⌊(B+1)ξ⌋ = z}` has measure `1/(B+1)`. Eq. (15)
holds for every `ξ ∈ [0, 1)` and is stated in `ℤ`. A coupling in (ii) is a nonnegative function
on `{0,…,B} × {0,…,D}` (`Fin (B+1) × Fin (D+1)`) whose marginals are the two uniform laws. -/
theorem lemma_4_9 (B D : ℕ) :
    ((∀ z : ℕ, z ≤ B →
        volume {ξ : ℝ | ξ ∈ Set.Ico (0 : ℝ) 1 ∧ ⌊((B : ℝ) + 1) * ξ⌋₊ = z} =
          ENNReal.ofReal (1 / ((B : ℝ) + 1))) ∧
      (∀ z : ℕ, z ≤ D →
        volume {ξ : ℝ | ξ ∈ Set.Ico (0 : ℝ) 1 ∧ ⌊((D : ℝ) + 1) * ξ⌋₊ = z} =
          ENNReal.ofReal (1 / ((D : ℝ) + 1))) ∧
      ∀ ξ ∈ Set.Ico (0 : ℝ) 1,
        |((⌊((B : ℝ) + 1) * ξ⌋₊ : ℕ) : ℤ) - ((⌊((D : ℝ) + 1) * ξ⌋₊ : ℕ) : ℤ)| +
          |((B : ℤ) - ((⌊((B : ℝ) + 1) * ξ⌋₊ : ℕ) : ℤ)) -
            ((D : ℤ) - ((⌊((D : ℝ) + 1) * ξ⌋₊ : ℕ) : ℤ))| =
          |(B : ℤ) - (D : ℤ)|) ∧
    ∀ (A C : ℕ) (h L : ℝ), 0 ≤ h → 0 ≤ L → |(A : ℝ) - (C : ℝ)| ≤ h →
      |(B : ℝ) - (D : ℝ)| ≤ h → L ≤ (B : ℝ) → L ≤ (D : ℝ) →
      ∃ q : Fin (B + 1) × Fin (D + 1) → ℝ,
        (∀ p, 0 ≤ q p) ∧
        (∀ z : Fin (B + 1), ∑ z' : Fin (D + 1), q (z, z') = 1 / ((B : ℝ) + 1)) ∧
        (∀ z' : Fin (D + 1), ∑ z : Fin (B + 1), q (z, z') = 1 / ((D : ℝ) + 1)) ∧
        ∑ p ∈ Finset.univ.filter (fun p : Fin (B + 1) × Fin (D + 1) =>
            A + (p.1 : ℕ) ≠ C + (p.2 : ℕ)), q p ≤ 3 * h / (L + 1) := by sorry

end KMPMixing
