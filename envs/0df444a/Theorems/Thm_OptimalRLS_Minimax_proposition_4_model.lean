-- Prove2me | Theorems.Thm_OptimalRLS_Minimax_proposition_4_model
-- name    : OptimalRLS.Minimax.proposition_4_model
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T19:31:16.436994+00:00
-- url     : https://prove2.me/theorems/704d67f1-155a-475c-954e-cd6f42a36fdb
-- title:
--   Proposition 4 (first part), p. 21 — ρ_f is a probability measure with marginal ν and regression function f, and ρ_f ∈ P(b, c) under (53)
-- statement:
--   Work in the setting of §5.3: $\dim Y = d < \infty$, Hypothesis 1 holds with constant $\kappa$, the constants $M, \Sigma, R, \alpha, \beta$ are positive, $1 < b$ and $1 \le c \le 2$. Let $\nu$ be a probability measure on $X$ whose operator $T$ has a spectral decomposition $T = \sum_{n \ge 1} t_n \langle\cdot, e_n\rangle e_n$ with $(e_n)$ orthonormal and decreasing $t_n > 0$ satisfying $\alpha \le n^b t_n \le \beta$ for all $n \ge 1$; this is exactly what one gets from the marginal $\nu$ of any $\rho_0 \in \mathcal P(b,c)$, as in (52).
--
--   Let $(v_j)_{j=1}^d$ be an orthonormal basis of $Y$, let $f = T^{(c-1)/2} g$ for some $g \in \mathcal H$ with $\|g\|^2_{\mathcal H} \le R$, and let $L = 4\sqrt{\kappa^c R}$. Let $\rho_f$ be the distribution on $X \times Y$ with marginal $\nu$ and conditional law
--   $$\rho_f(y\mid x) = \frac{1}{2dL} \sum_{j=1}^d \Big( (L - \langle f, K_x v_j\rangle)\, \delta_{-dLv_j} + (L + \langle f, K_x v_j\rangle)\, \delta_{+dLv_j} \Big).$$
--   Then:
--   1. $\rho_f$ is a probability measure on $X \times Y$;
--   2. its marginal distribution on $X$ is $\nu$;
--   3. its regression function is $f$: $\int_Y y \, d\rho_f(y\mid x) = f(x)$ for $\nu$-almost every $x$;
--   4. if moreover
--   $$\min(M, \Sigma) \ge 2(4d+1)\sqrt{\kappa^c R} \qquad (53),$$
--   then $\rho_f \in \mathcal P(b,c)$.
--
--   These distributions are the hypotheses of the lower-bound argument: they all share the marginal $\nu$, so their excess risks are distances $\|\sqrt T(\cdot - f)\|^2$, and they all belong to the prior.
--
--   **Formalization Note.** The setting assumption "$\nu$ is the marginal of some $\rho_0 \in \mathcal P(b,c)$" is stated directly as the existence of the eigen-system with (17); conversely $\nu \otimes \delta_0 \in \mathcal P(b,c)$ for any such $\nu$, so nothing is lost. The eigenvalues are indexed from $0$ in Lean: `t n` is the paper's $t_{n+1}$. The basis of $Y$ is taken orthonormal. The conditional law is Mathlib's `condKernel` of $\rho_f$. The proof's variance display on p. 22 is not correct for $d \ge 2$ (the second moment is $d^2L^2 - \|f(x)\|^2$), but the conclusion still holds; a proof should not rely on that display.
-- source:
--   Caponnetto & De Vito, Found. Comput. Math. 7 (2007), authors' copy, Proposition 4 (first part, through (53)), p. 21; proof pp. 21–22; setting §5.3 and (52), pp. 20–21

import Mathlib
import Definitions.Def_OptimalRLS_Minimax_Setting

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace OptimalRLS.Minimax

/-- **Proposition 4** (first part), Caponnetto & De Vito (2007), p. 21. Fix the setting of §5.3:
`dim Y = d < +∞` (`d = Module.finrank ℝ Y`), Hypothesis 1 with constant `κ`, constants
`M, Σ (Sig), R, α, β > 0`, `1 < b`, `1 ≤ c ≤ 2`, and a probability measure `ν` on `X` whose operator `T`
has the spectral decomposition (52) `T = ∑ₙ tₙ ⟨·, eₙ⟩ eₙ` with decreasing `tₙ` satisfying (17)
`α ≤ nᵇ tₙ ≤ β` (index shift: the paper's `tₙ` is `t (n - 1)`). This is exactly what "ν is the marginal
of some `ρ₀ ∈ P(b, c)`" provides, and conversely `ν ⊗ δ₀ ∈ P(b, c)` for every such `ν`.

Let `(vⱼ)` be an orthonormal basis of `Y`, `f = T^{(c−1)/2} g` with `‖g‖² ≤ R`, and `L = 4√(κ^c R)`.
Then `ρ_f` (`rhoF`) is a probability measure, its marginal is `ν`, its regression function
`x ↦ ∫ y dρ_f(y|x)` equals `f` (`ν`-a.e.), and under (53) `min(M, Σ) ≥ 2(4d + 1)√(κ^c R)` it belongs
to `P(b, c)`. -/
theorem proposition_4_model
    {X Y H : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    [TopologicalSpace.SeparableSpace Y] [MeasurableSpace Y] [BorelSpace Y] [FiniteDimensional ℝ Y]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H] [RKHS ℝ H X Y]
    {ι : Type*} (κ : ℝ) (v : HilbertBasis ι ℝ Y) (h1 : Hyp1 H κ v)
    (M Sig R α β b c : ℝ) (hM : 0 < M) (hSig : 0 < Sig) (hR : 0 < R) (hα : 0 < α) (hβ : 0 < β)
    (hb : 1 < b) (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (ν : Measure X) [IsProbabilityMeasure ν] (e : ℕ → H) (t : ℕ → ℝ)
    (heig : IsEigenSystem ν e t) (hanti : Antitone t)
    (h17 : ∀ n : ℕ, α ≤ ((n : ℝ) + 1) ^ b * t n ∧ ((n : ℝ) + 1) ^ b * t n ≤ β)
    (vb : OrthonormalBasis (Fin (Module.finrank ℝ Y)) ℝ Y)
    (g : H) (hg : ‖g‖ ^ 2 ≤ R) (f : H) (hf : f = Tpow e t ((c - 1) / 2) g) :
    ∃ _ : IsProbabilityMeasure (rhoF ν vb (Lconst κ c R) f),
      (rhoF ν vb (Lconst κ c R) f).fst = ν ∧
      (∀ᵐ x ∂ν, ∫ y, y ∂((rhoF ν vb (Lconst κ c R) f).condKernel x) = f x) ∧
      (2 * (4 * (Module.finrank ℝ Y : ℝ) + 1) * Real.sqrt (κ ^ c * R) ≤ min M Sig →
        InPrior H M Sig R α β b c (rhoF ν vb (Lconst κ c R) f)) := by sorry

end OptimalRLS.Minimax
