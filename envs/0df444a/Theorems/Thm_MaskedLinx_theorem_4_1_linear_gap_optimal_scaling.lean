-- Prove2me | Theorems.Thm_MaskedLinx_theorem_4_1_linear_gap_optimal_scaling
-- name    : MaskedLinx.theorem_4_1_linear_gap_optimal_scaling
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:41:46.21673+00:00
-- url     : https://prove2.me/theorems/4d4ac48e-8676-4ddd-873e-860971d071cc
-- title:
--   Theorem 4.1 — the identity mask lowers the optimally scaled linx bound by at least $0.024036\,n$ (corrected: $n\ge4$)
-- statement:
--   There are a constant $b\ge0.024036$ and positive semidefinite matrices $C_n$ of order $n$ such that, for every even $n\ge4$ and $s=n/2$,
--
--   $$\min_{\gamma>0}\mathrm{linx}\big(C_n,\tfrac n2;\gamma\big)-\min_{\bar\gamma>0}\mathrm{linx}\big(C_n,\tfrac n2;I,\bar\gamma\big)\ \ge\ b\,n .$$
--
--   Here $\mathrm{linx}(C,s;\gamma)$ is the scaled linx bound and $\mathrm{linx}(C,s;I,\bar\gamma)=\mathrm{linx}(C\circ I,s;\bar\gamma)$ is the scaled bound masked with the identity mask $I$. In full, for every even $n\ge4$:
--
--   1. $C_n$ is positive semidefinite, its diagonal entries are positive, and $n/2\le\mathrm{rank}(C_n)$ (the paper's standing assumptions for the maximum-entropy sampling problem with $s=n/2$);
--   2. both minima are attained: there are $\gamma_1>0$ minimizing $\gamma\mapsto\mathrm{linx}(C_n,\tfrac n2;\gamma)$ and $\gamma_2>0$ minimizing $\bar\gamma\mapsto\mathrm{linx}(C_n\circ I,\tfrac n2;\bar\gamma)$ over the positive reals;
--   3. both minimum values are real numbers $v_1,v_2$, and $b\,n\le v_1-v_2$.
--
--   Masking with $I$ discards all correlations; the theorem says that, even when both bounds use their own optimal scaling parameter, this can improve the linx bound on the maximum-entropy sampling value by an amount linear in $n$.
--
--   **Formalization Note** The identity mask enters as the Hadamard product `C n ⊙ 1`; $n/2$ is natural-number division, exact for even $n$; $0.024036$ is the exact rational $24036/10^6$. Requiring the minimum values to be real excludes `EReal` subtraction artifacts.
--
--   Differences from the source:
--   - correction: the sequence is indexed by 𝓘, the even integers (Theorem 2.12, p.7) → every even n ≥ 4; reason: n = 2 is false. For PSD C = [[a,c],[c,b]], a ≥ b, s = 1: if C is positive definite, Propositions 3.2 and 3.1 give both minima = log a; if C has rank 1, linx(C,1;γ) ≥ z(C,1) = log a while Theorem 3.8 makes its limit log a; if c = 0, C ∘ I = C. So no C₂ has gap ≥ 2b > 0
--   - encoding: min over γ > 0 of an EReal-valued linx; sequence {Cₙ} → explicit minimizers γ₁, γ₂ > 0 with real minimum values v₁, v₂, ldet = ⊥ off the positive definite matrices, linx an EReal supremum, Cₙ a function of n used at even n ≥ 4; reason: the paper's min asserts attainment; real values avoid EReal subtraction junk
--   - generalization: PSD matrices Cₙ → PSD with positive diagonal and n/2 ≤ rank(Cₙ); reason: the witnesses must also satisfy §1's standing assumptions for s = n/2, which the paper's Cₙ do; this only adds to the conclusion
-- source:
--   Chen, Fampa, Lee, Masking Anstreicher's linx bound for improved entropy bounds, arXiv:2106.02980v1, Theorem 4.1, p.13 (index set 𝓘 from Theorem 2.12, p.7; masked bound from display (3), p.3)

import Mathlib
import Definitions.Def_MaskedLinx_linx

open Matrix

namespace MaskedLinx

/-- **Theorem 4.1 (the identity mask lowers the optimally scaled linx bound linearly in `n`)
(corrected: `n ≥ 4`).**
Chen, Fampa, Lee, *Masking Anstreicher's linx bound for improved entropy bounds*,
arXiv:2106.02980v1, Theorem 4.1, p.13:
"There is an infinite sequence of positive-semidefinite matrices {Cₙ}ₙ∈𝓘, such that
min_{γ>0} linx(Cₙ, n/2; γ) − min_{γ̄>0} linx(Cₙ, n/2; I, γ̄) ≥ bn
for some positive scalar b ≥ 0.024036."
Here 𝓘 is the set of even integers (Theorem 2.12, p.7) and `I` is the identity mask, so
`linx(Cₙ, n/2; I, γ̄) = linx(Cₙ ∘ I, n/2; γ̄)` (display (3), p.3).

Statement: there are `b ≥ 0.024036` and matrices `C n` of order `n` such that for every even
`n ≥ 4`, with `s = n/2`: `C n` is positive semidefinite with positive diagonal and
`n/2 ≤ rank (C n)`; both minima over the scaling parameter are attained, at `γ₁ > 0` (unmasked)
and `γ₂ > 0` (masked with `I`); both minimum values are real numbers `v₁, v₂`; and
`b·n ≤ v₁ − v₂`.

**Formalization Note.** The identity mask enters as the Hadamard product `C n ⊙ 1`. `n / 2` is
natural-number division, exact for even `n`. `0.024036` is the exact rational `24036/10⁶`.
The case `n = 2` of the even integers is excluded: it is false (no PSD `2 × 2` matrix has a
positive gap). Requiring the minimum values to be real rules out `EReal` subtraction junk. -/
theorem theorem_4_1_linear_gap_optimal_scaling :
    ∃ b : ℝ, (0.024036 : ℝ) ≤ b ∧ ∃ C : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ,
      ∀ n : ℕ, Even n → 4 ≤ n →
        (C n).PosSemidef ∧ (∀ j, 0 < C n j j) ∧ n / 2 ≤ (C n).rank ∧
        ∃ γ₁ : ℝ, 0 < γ₁ ∧ ∃ γ₂ : ℝ, 0 < γ₂ ∧
          (∀ γ : ℝ, 0 < γ → linx (C n) (n / 2) γ₁ ≤ linx (C n) (n / 2) γ) ∧
          (∀ γ : ℝ, 0 < γ → linx (C n ⊙ 1) (n / 2) γ₂ ≤ linx (C n ⊙ 1) (n / 2) γ) ∧
          ∃ v₁ v₂ : ℝ, linx (C n) (n / 2) γ₁ = (v₁ : EReal) ∧
            linx (C n ⊙ 1) (n / 2) γ₂ = (v₂ : EReal) ∧ b * n ≤ v₁ - v₂ := by sorry

end MaskedLinx
