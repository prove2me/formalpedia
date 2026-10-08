-- Prove2me | Theorems.Thm_OptimalRLS_Individual_pprime_subset
-- name    : OptimalRLS.Individual.pprime_subset
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:19:11.544095+00:00
-- url     : https://prove2.me/theorems/2eeb8f06-7593-46ff-8edc-f5a9d1255276
-- title:
--   Proof of Th. 3, pp. 26–27 — P′ ⊂ P(b, c): every Gaussian-noise distribution ρ_s with mean m^(s) belongs to the prior
-- statement:
--   Assume Hypothesis 1 with constant $\kappa$, and let $\dim Y = d < \infty$. Fix positive constants $M, \Sigma, R, \alpha, \beta$, and let $1 < b < B$ and $1 \le c \le 2$.
--
--   Let $\nu$ be a probability measure on $X$ whose operator $T$ has an eigen-system $(t_n, e_n)_{n \ge 1}$ with $t_1 \ge t_2 \ge \dots > 0$ and
--   $$\alpha \le n^b t_n \le \beta \qquad (n \ge 1).$$
--   Put $\epsilon = (B - b)c$ and $\gamma_n = n^{-(bc + \epsilon + 1)} \frac{\epsilon}{\epsilon+1}\alpha^c R$.
--
--   Then for every sign sequence $s \in \{+1, -1\}^\infty$, the distribution $\rho_s$ belongs to $\mathcal P(b, c)$. Here $\rho_s$ has marginal $\nu$ and conditional distribution $\mathcal N(m^{(s)}(x), \sigma^2 \mathrm{Id})$, with $m^{(s)} = \sum_n s_n \sqrt{t_n^{-1}\gamma_n}\, e_n$ and $\sigma^2$ as in the proof of Theorem 3.
--
--   In particular the minimal-norm risk minimizer of $\rho_s$ is $m^{(s)}$. The source condition $m^{(s)} = T^{(c-1)/2} g$ holds with $\|g\|^2 \le R$, and the Gaussian noise satisfies the moment condition (9).
--
--   This shows that the subset $\mathcal P'$ on which the lower bound is proved lies inside the prior, so a lower rate over $\mathcal P'$ is a lower rate over $\mathcal P(b, c)$.
--
--   **Formalization Note** The page fixes $\rho_0 \in \mathcal P(b, c)$ and takes $\nu$ to be its marginal. The statement assumes only what that provides: a probability measure $\nu$ with an eigen-system of $T$ satisfying (17) with nonincreasing eigenvalues. Indices are shifted to start at $0$. Membership in $\mathcal P(b, c)$ is `InPrior`, which includes "probability measure".
-- source:
--   Caponnetto & De Vito, Found. Comput. Math. 7 (2007), authors' copy, Proof of Th. 3, pp. 26–27, display "It is simple to check that P′ ⊂ P(b, c)" and the moment computation that follows

import Mathlib
import Definitions.Def_OptimalRLS_Individual_Model

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal

namespace OptimalRLS.Individual

variable {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [TopologicalSpace.SeparableSpace Y] [MeasurableSpace Y] [BorelSpace Y] [FiniteDimensional ℝ Y]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H] [RKHS ℝ H X Y]

/-- **`P′ ⊂ P(b, c)`** (proof of Theorem 3, pp. 26–27). Let `ν` be a probability measure on `X`
whose operator `T` has an eigen-system `(t_n, e_n)_{n ≥ 1}` with `N = +∞`, nonincreasing
eigenvalues and (17) `α ≤ n^b t_n ≤ β` (what "`ρ₀ ∈ P(b, c)`, `ν` its marginal, (52)" provides).
Let `B > b`, `ε = (B − b)c`, `γ_n = n^{−(bc+ε+1)}(ε/(ε+1))α^c R`, and `d = dim Y`. Then for every
sign sequence `s ∈ {+1, −1}^∞`, the distribution with marginal `ν` and conditional
`ρ(y|x) = N(m^{(s)}(x), σ² Id)` belongs to `P(b, c)`. -/
theorem pprime_subset {ι : Type*} (κ : ℝ) (v : HilbertBasis ι ℝ Y) (h1 : Hyp1 X H κ v)
    (M Sig R α β : ℝ) (hM : 0 < M) (hSig : 0 < Sig) (hR : 0 < R) (hα : 0 < α) (hβ : 0 < β)
    (b c : ℝ) (hb : 1 < b) (hc1 : 1 ≤ c) (hc2 : c ≤ 2) (B : ℝ) (hB : b < B)
    (ν : Measure X) [IsProbabilityMeasure ν] (e : ℕ → H) (t : ℕ → ℝ)
    (heig : IsEigenSystem ν e t) (hanti : Antitone t)
    (h17 : ∀ n : ℕ, α ≤ ((n : ℝ) + 1) ^ b * t n ∧ ((n : ℝ) + 1) ^ b * t n ≤ β)
    (s : ℕ → ℝ) (hs : ∀ n, s n = 1 ∨ s n = -1) :
    InPrior (H := H) M Sig R α β b c
      (rhoS ν (mS e t (gam b c ((B - b) * c) α R) s) (sig2 M Sig (Module.finrank ℝ Y))) := by sorry

end OptimalRLS.Individual
