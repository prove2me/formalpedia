-- Prove2me | Theorems.Thm_OptimalRLS_Minimax_proposition_5
-- name    : OptimalRLS.Minimax.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T19:31:29.519129+00:00
-- url     : https://prove2.me/theorems/f4f34eae-06b5-4399-a131-d776d32bc445
-- title:
--   Proposition 5, pp. 22–23 — e^(γε^(−1/(bc))) functions fᵢ = T^((c−1)/2)gᵢ with ε ≤ ‖√T(fᵢ − fⱼ)‖² ≤ 4ε
-- statement:
--   Fix $R > 0$, $\alpha > 0$, $1 < b$ and $1 \le c \le 2$. There is a constant $\gamma > 0$, depending only on these numbers, with the following property. Work in the setting of §5.3 ($\dim Y < \infty$, Hypothesis 1 with some $\kappa$), and let $\nu$ be a probability measure on $X$ whose operator $T = \sum_{n \ge 1} t_n \langle \cdot, e_n\rangle e_n$ has orthonormal $(e_n)$ and decreasing eigenvalues with
--   $$t_n \ge \frac{\alpha}{n^b} \qquad (n \ge 1),$$
--   as in (52). Then there is $\epsilon_0 > 0$ such that for every $0 < \epsilon \le \epsilon_0$ there are $N_\epsilon \in \mathbb N$ and $f_1, \dots, f_{N_\epsilon} \in \mathcal H$ with:
--   1. for every $i$, $f_i = T^{(c-1)/2} g_i$ for some $g_i \in \mathcal H$ with $\|g_i\|^2_{\mathcal H} \le R$;
--   2. for all $i \ne j$,
--   $$\epsilon \le \big\|\sqrt T (f_i - f_j)\big\|^2_{\mathcal H} \le 4\epsilon \qquad (56);$$
--   3. $$N_\epsilon \ge e^{\gamma \epsilon^{-1/(bc)}} \qquad (57).$$
--
--   Here $\|\sqrt T h\|^2_{\mathcal H} = \int_X \|h(x)\|^2_Y\, d\nu(x)$. The proposition provides exponentially many hypotheses inside the source class that are pairwise separated, but not too far apart, in the excess-risk distance; this is what fixes the exponent $bc/(bc+1)$ of the lower rate.
--
--   **Formalization Note.** The constant $\gamma$ is quantified before the spaces, the kernel constant $\kappa$ and the measure $\nu$, which expresses "depending only on $R$ and $\alpha$" (and on the fixed $b, c$); the spaces range over one universe. Only the lower half of (17) is assumed, as in (52). Condition (56) is required for $i \ne j$: for $i = j$ the left inequality would read $\epsilon \le 0$. The eigenvalues are indexed from $0$ in Lean: `t n` is the paper's $t_{n+1}$, and the hypothesis reads $\alpha \le (n+1)^b\, t_n$.
-- source:
--   Caponnetto & De Vito, Found. Comput. Math. 7 (2007), authors' copy, Proposition 5, (56)–(57), pp. 22–23; proof p. 23

import Mathlib
import Definitions.Def_OptimalRLS_Minimax_Setting

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

universe u

namespace OptimalRLS.Minimax

/-- **Proposition 5**, Caponnetto & De Vito (2007), pp. 22–23. Fix `R, α > 0`, `1 < b`, `1 ≤ c ≤ 2`.
There is a constant `γ > 0`, depending only on these (in particular not on the spaces, on `κ` or on
`ν`), such that in the setting of §5.3 — Hypothesis 1, `ν` a probability measure on `X` whose
operator `T` has the spectral decomposition (52) `T = ∑ₙ tₙ ⟨·, eₙ⟩ eₙ` with decreasing
`tₙ ≥ α/nᵇ` (index shift: the paper's `tₙ` is `t (n - 1)`) — there is `ε₀ > 0` such that for all
`0 < ε ≤ ε₀` there are `N_ε` and `f₁, …, f_{N_ε} ∈ H` with
i) `fᵢ = T^{(c−1)/2} gᵢ`, `‖gᵢ‖² ≤ R`;
ii) (56) `ε ≤ ‖√T(fᵢ − fⱼ)‖²_H ≤ 4ε` for `i ≠ j` (`‖√T h‖²_H` is `covForm ν h h`);
iii) (57) `N_ε ≥ e^{γ ε^{−1/(bc)}}`.
Only the lower half of (17) is assumed, as in (52). -/
theorem proposition_5 (R α b c : ℝ) (hR : 0 < R) (hα : 0 < α)
    (hb : 1 < b) (hc1 : 1 ≤ c) (hc2 : c ≤ 2) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ {X Y H : Type u} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
        [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
        [TopologicalSpace.SeparableSpace Y] [MeasurableSpace Y] [BorelSpace Y]
        [FiniteDimensional ℝ Y]
        [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H] [RKHS ℝ H X Y]
        {ι : Type u} (κ : ℝ) (v : HilbertBasis ι ℝ Y), Hyp1 H κ v →
      ∀ (ν : Measure X) [IsProbabilityMeasure ν] (e : ℕ → H) (t : ℕ → ℝ),
        IsEigenSystem ν e t → Antitone t → (∀ n : ℕ, α ≤ ((n : ℝ) + 1) ^ b * t n) →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
          ∃ N : ℕ, ∃ f : Fin N → H,
            (∀ i, ∃ g : H, f i = Tpow e t ((c - 1) / 2) g ∧ ‖g‖ ^ 2 ≤ R) ∧
            (∀ i j, i ≠ j → ε ≤ covForm ν (f i - f j) (f i - f j) ∧
              covForm ν (f i - f j) (f i - f j) ≤ 4 * ε) ∧
            Real.exp (γ * ε ^ (-(1 / (b * c)))) ≤ N := by sorry

end OptimalRLS.Minimax
