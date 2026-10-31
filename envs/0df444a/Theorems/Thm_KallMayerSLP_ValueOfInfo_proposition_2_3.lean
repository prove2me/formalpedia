-- Prove2me | Theorems.Thm_KallMayerSLP_ValueOfInfo_proposition_2_3
-- name    : KallMayerSLP.ValueOfInfo.proposition_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:14:52.839277+00:00
-- url     : https://prove2.me/theorems/c3e66f2c-04c3-4344-af65-2f5223edf6b6
-- title:
--   Proposition 2.3 — $EV\le WS$ when only $h(\cdot)$ is random
-- statement:
--   This is Proposition 2.3 of Kall & Mayer, Chapter 3.
--
--   Let $\xi$ be a random vector in $\mathbb R^r$ with $\xi\in L^2$, and consider the two-stage recourse problem in which only the right-hand side $h(\xi)=h+\sum_j h^j\xi_j$ is random, while $A,b,c,T,W,q$ are deterministic. Then the optimal value of the expected value problem is at most the wait-and-see value:
--
--   $$
--   EV\le WS .
--   $$
--
--   Combined with Proposition 2.2 this places $EV$ below both $WS$ and $RS$; the book notes (citing Birge–Louveaux) that the inequality cannot be expected for more general recourse functions.
--
--   **Formalization Note** $EV$ and $WS$ are extended reals; no finiteness hypothesis.
--
--   Differences from the source:
--   - encoding: random vector ξ on a probability space (Ω, 𝓕, P) with ξ ∈ L²(Ω, ℝʳ) (Assumption 1.1) → a probability measure μ on ℝʳ (the law ℙ_ξ) whose coordinates are in L²(μ); reason: every quantity of §2.3 depends on ξ only through its law
--   - encoding: min and 𝔼 of values that may be ±∞; 𝔼 undefined for ∞ − ∞ (p.200) → EReal infima; expectation eExp = ∫f⁺ − ∫f⁻, and +∞ when ∫f⁺ = +∞; reason: the book's convention of p.200 (an undefined expected recourse is never chosen); the values agree with the book's wherever the book's are defined
--   - encoding: recourse function Q(x; h(ξ)): only h(·) random → TwoStageSLP.ofRandomH with deterministic T, W, q; reason: the book's notation p.200: T(·) ≡ T, W(·) ≡ W, q(·) ≡ q
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, Proposition 2.3, p.245 (PDF 254)

import Mathlib
import Definitions.Def_KallMayerSLP_ValueOfInfo_WS
import Definitions.Def_KallMayerSLP_ValueOfInfo_EV

open MeasureTheory

namespace KallMayerSLP.ValueOfInfo

/-- **Proposition 2.3: `EV ≤ WS` when only `h(·)` is random.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, Proposition 2.3, p.245 (PDF 254):
"Given the recourse function `Q(x; h(ξ))` (i.e. only the right-hand-side `h(·)` is random) it follows
that `EV ≤ WS`."

`μ` is the law of `ξ` on `ℝʳ`, a probability measure with `ξ ∈ L²` (Chapter 3, Assumption 1.1); the
problem has deterministic `A, b, c, T, W, q` and affine `h(ξ) = h + Σⱼ hʲ ξⱼ`.

**Formalization Note.** `EV` and `WS` are `EReal`-valued; no finiteness hypothesis. -/
theorem proposition_2_3 {r n₁ m₁ n₂ m₂ : ℕ} (μ : Measure (Fin r → ℝ)) [IsProbabilityMeasure μ]
    (hξ : ∀ j, MemLp (fun ξ : Fin r → ℝ => ξ j) 2 μ)
    (A : Matrix (Fin m₁) (Fin n₁) ℝ) (b : Fin m₁ → ℝ) (c : Fin n₁ → ℝ)
    (T : Matrix (Fin m₂) (Fin n₁) ℝ) (W : Matrix (Fin m₂) (Fin n₂) ℝ) (h₀ : Fin m₂ → ℝ)
    (hc : Fin r → Fin m₂ → ℝ) (q : Fin n₂ → ℝ) :
    EV (TwoStageSLP.ofRandomH A b c T W h₀ hc q) μ ≤
      WS (TwoStageSLP.ofRandomH A b c T W h₀ hc q) μ := by sorry

end KallMayerSLP.ValueOfInfo
