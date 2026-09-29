-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_gt_and_hermiteSum_GammaR_mul_mellin_ne_zero_of_shift_ratio_real_of_parity
-- name    : LanglandsTunnell.exists_gt_and_hermiteSum_GammaR_mul_mellin_ne_zero_of_shift_ratio_real_of_parity
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/a94414dc-ef33-579c-94a6-cecb3508cc76
-- title:
--   Non-vanishing of a finite Hermite sum on the real ray
-- statement:
--   Fix a natural number $m$, a non-zero rational $a$, a complex number $u_3$, classes $a_3, c \in \mathbb{Z}/2$ and an integer $e$. Let $S$ be the set of quadruples $T = ((r,i),(j,l))$ with $r,i,j,l \le m$ subject to $i + j + l + 2r = m$ together with the two parity conditions $j \equiv a_3 + c + m$ and $l \equiv e + c$ in $\mathbb{Z}/2$, and assume $S$ is non-empty. Let $H : \mathbb{N} \to \mathbb{R} \to \mathbb{C}$ be a family of functions and write $M_j(s) =$ `mellin (H j) s`. Assume: (i) for every index $j$ and every $\varepsilon > 0$ there is $R$ such that for all real $x \ge R$ one has $M_j(x) \neq 0$ and $\|M_j(x+2) - \frac{x}{2\pi a^2} M_j(x)\| \le \varepsilon\, x\, \|M_j(x)\|$; (ii) for every $j$ there are constants $C, R$ with $\|M_{j+2}(x)\| \le C \|M_j(x)\|$ for all real $x \ge R$. Then for every real $\sigma_0$ there exists a real $s > \sigma_0$ with $$\sum_{T \in S} \frac{(-1)^r\, m!\, a^l}{r!\, i!\, j!\, l!\, (4\pi)^r}\, \Gamma_{\mathbb{R}}(s + u_3 + i)\, M_j(s + l - 1) \neq 0,$$ where $\Gamma_{\mathbb{R}}$ is `Complex.Gammaℝ`.
--
--   This is the dominance, or non-vanishing, step for the finite Hermite-type sum of Gamma factors times Mellin transforms that arises in the weight-zero parity shape of the archimedean zeta computation: the hypotheses say that along the real ray each single-sheet transform is non-zero and satisfies an approximate shift relation $M_j(x+2) \approx \frac{x}{2\pi a^2} M_j(x)$ with a double-step comparison bound, and the conclusion extracts a real point arbitrarily far to the right at which the whole sum survives. It is used to close the corresponding admissible-twist non-vanishing statement in the cubic induction, [`LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_archZeta30_jacquetVector3_ne_zero_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_weightZeroLevi`](thm.html#LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_archZeta30_jacquetVector3_ne_zero_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_weightZeroLevi).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_gt_and_hermiteSum_GammaR_mul_mellin_ne_zero_of_shift_ratio_real_of_parity.lean

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Complex

theorem LanglandsTunnell.exists_gt_and_hermiteSum_GammaR_mul_mellin_ne_zero_of_shift_ratio_real_of_parity
    (m : ℕ) (a : ℚ) (ha : a ≠ 0) (u₃ : ℂ) (a₃ c : ZMod 2) (e : ℤ)
    (hne : (((Finset.range (m + 1) ×ˢ Finset.range (m + 1)) ×ˢ (Finset.range (m + 1) ×ˢ Finset.range (m + 1))).filter
          (fun T : (ℕ × ℕ) × (ℕ × ℕ) => T.1.2 + T.2.1 + T.2.2 + 2 * T.1.1 = m ∧
            ((T.2.1 : ZMod 2) = a₃ + c + (m : ZMod 2)) ∧ ((T.2.2 : ZMod 2) = (e : ZMod 2) + c))).Nonempty)
    (H : ℕ → ℝ → ℂ)
    (hA : ∀ (j : ℕ) (ε : ℝ), 0 < ε → ∃ R : ℝ, ∀ x : ℝ, R ≤ x →
      mellin (H j) (x : ℂ) ≠ 0 ∧
      ‖mellin (H j) ((x : ℂ) + 2) - (x : ℂ) / (2 * (Real.pi : ℂ) * (a : ℂ) ^ 2) * mellin (H j) (x : ℂ)‖ ≤ ε * x * ‖mellin (H j) (x : ℂ)‖)
    (hC : ∀ (j : ℕ), ∃ C R : ℝ, ∀ x : ℝ, R ≤ x →
      ‖mellin (H (j + 2)) (x : ℂ)‖ ≤ C * ‖mellin (H j) (x : ℂ)‖) :
    ∀ σ₀ : ℝ, ∃ s : ℝ, σ₀ < s ∧
      ∑ T ∈ ((Finset.range (m + 1) ×ˢ Finset.range (m + 1)) ×ˢ (Finset.range (m + 1) ×ˢ Finset.range (m + 1))).filter
              (fun T : (ℕ × ℕ) × (ℕ × ℕ) => T.1.2 + T.2.1 + T.2.2 + 2 * T.1.1 = m ∧
            ((T.2.1 : ZMod 2) = a₃ + c + (m : ZMod 2)) ∧ ((T.2.2 : ZMod 2) = (e : ZMod 2) + c)),
            ((-1 : ℂ) ^ T.1.1 * (m.factorial : ℂ) * (a : ℂ) ^ T.2.2 /
                ((T.1.1.factorial : ℂ) * (T.1.2.factorial : ℂ) * (T.2.1.factorial : ℂ) * (T.2.2.factorial : ℂ) *
                  (4 * (Real.pi : ℂ)) ^ T.1.1)) *
              Complex.Gammaℝ ((s : ℂ) + u₃ + (T.1.2 : ℂ)) * mellin (H T.2.1) ((s : ℂ) + (T.2.2 : ℂ) - 1) ≠ 0 := by sorry
