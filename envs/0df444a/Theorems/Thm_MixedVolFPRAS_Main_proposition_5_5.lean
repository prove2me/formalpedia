-- Prove2me | Theorems.Thm_MixedVolFPRAS_Main_proposition_5_5
-- name    : MixedVolFPRAS.Main.proposition_5_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:32:13.504383+00:00
-- url     : https://prove2.me/theorems/a55505eb-24a9-43f6-86db-bf3fe9a2d474
-- title:
--   Proposition 5.5 — the box-constrained capacity program (16) is convex, attains its minimum, and every minimizer gives V ≤ Z_β(t*)/∏t*ᵢ ≤ V/(1 − 2n²β)
-- statement:
--   Under the assumptions of Lemma 5.2 (convex bodies $K_i$ with $r_iB_2^n\subseteq K_i\subseteq R_iB_2^n$, $r_i>0$, $R=\max_iR_i$), let $0\le\beta<1/(2n^2)$ and $\mathcal B=\prod_{i=1}^n[0,\log(R/r_i)]$. The convex program
--
--   $$\min_{y\in\mathcal B}\ \big\{\log Z_\beta(e^y)-\langle y,\mathbf 1\rangle\big\}\tag{16}$$
--
--   attains its minimum, and every minimizer $y^*$, with $t^*=e^{y^*}$ (coordinatewise), satisfies
--
--   $$V_n(K_1,\dots,K_n)\le\frac{Z_\beta(t^*)}{\prod_it^*_i}\le\frac{V_n(K_1,\dots,K_n)}{1-2n^2\beta}.$$
--
--   So minimizing a Gurvits-type capacity over a box of polynomial diameter yields a rescaling at which $Z_\beta$ — computable by Theorem 4.1 after one common affine rounding — determines $V_n(K)$ up to $1+O(n^2\beta)$.
--
--   Differences from the source:
--   - reading: "the convex program (16)" → convexity of the objective on $\mathcal B$ is a conclusion (`ConvexOn ℝ 𝔅 F`); reason: the statement calls (16) a convex program, and the proof's first sentence asserts it.
--   - reading: "under the assumptions of Lemma 5.2" → also $r_i>0$; reason: as in Lemma 5.2, the radii come from Definition 1.1.
--   - encoding: "attains its minimum", "every minimizer" → `∃ y ∈ 𝔅, IsMinOn F 𝔅 y` and `∀ y ∈ 𝔅, IsMinOn F 𝔅 y → …`; $R=\max_iR_i$ as `⨆ j, Rr j`; reason: Mathlib forms of the same notions.
-- source:
--   Chen, Liu, An FPRAS for Mixed Volumes, STOC 2027 submission (manuscript sha256 0acf8d97…), p. 24, Proposition 5.5

import Mathlib
import Definitions.Def_MixedVolFPRAS_Main_MixedVolume
import Definitions.Def_MixedVolFPRAS_Main_Balancing

open scoped Pointwise

namespace MixedVolFPRAS.Main

/-- **Proposition 5.5.** Under the assumptions of Lemma 5.2 (`rᵢ B₂ⁿ ⊆ Kᵢ ⊆ Rᵢ B₂ⁿ`,
`R = maxᵢ Rᵢ`), let `0 ≤ β < 1/(2n²)` and `𝔅 = ∏ᵢ [0, log(R/rᵢ)]`. The convex program
`min_{y ∈ 𝔅} {log Z_β(e^y) − ⟨y, 1⟩}` (16) attains its minimum, and every minimizer `y*`, with
`t* = e^{y*}`, satisfies `Vₙ(K) ≤ Z_β(t*)/∏ᵢ t*ᵢ ≤ Vₙ(K)/(1 − 2n²β)`. -/
theorem proposition_5_5 {n : ℕ} (K : Fin n → Set (E n)) (r Rr : Fin n → ℝ)
    (hK : ∀ i, IsConvexBody (K i)) (hr : ∀ i, 0 < r i)
    (hin : ∀ i, r i • unitBall n ⊆ K i) (hout : ∀ i, K i ⊆ Rr i • unitBall n)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ : β < 1 / (2 * (n : ℝ) ^ 2)) :
    ConvexOn ℝ {y : Fin n → ℝ | ∀ i, 0 ≤ y i ∧ y i ≤ Real.log ((⨆ j, Rr j) / r i)}
        (fun y => Real.log (Zbeta K β (fun i => Real.exp (y i))) - ∑ i, y i) ∧
      (∃ y ∈ {y : Fin n → ℝ | ∀ i, 0 ≤ y i ∧ y i ≤ Real.log ((⨆ j, Rr j) / r i)},
        IsMinOn (fun y => Real.log (Zbeta K β (fun i => Real.exp (y i))) - ∑ i, y i)
          {y : Fin n → ℝ | ∀ i, 0 ≤ y i ∧ y i ≤ Real.log ((⨆ j, Rr j) / r i)} y) ∧
      ∀ y ∈ {y : Fin n → ℝ | ∀ i, 0 ≤ y i ∧ y i ≤ Real.log ((⨆ j, Rr j) / r i)},
        IsMinOn (fun y => Real.log (Zbeta K β (fun i => Real.exp (y i))) - ∑ i, y i)
          {y : Fin n → ℝ | ∀ i, 0 ≤ y i ∧ y i ≤ Real.log ((⨆ j, Rr j) / r i)} y →
        mixedVolume K ≤ Zbeta K β (fun i => Real.exp (y i)) / ∏ i, Real.exp (y i) ∧
          Zbeta K β (fun i => Real.exp (y i)) / ∏ i, Real.exp (y i) ≤
            mixedVolume K / (1 - 2 * (n : ℝ) ^ 2 * β) := by sorry

end MixedVolFPRAS.Main
