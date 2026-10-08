-- Prove2me | Theorems.Thm_JacodTodorov10_LLN_eq_8_11
-- name    : JacodTodorov10.LLN.eq_8_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:21:07.527928+00:00
-- url     : https://prove2.me/theorems/2b4808f8-4657-4860-9da9-4cc91b6a1bb7
-- title:
--   (8.11) — E(|Δⁿᵢ X|² | 𝓕_{(i−1)Δₙ}) ≤ KΔₙ, with K uniform
-- statement:
--   Assume (H-$r$), (K-$v$) and the localized bound (8.3) with constant $C$ and functions $\gamma,\widehat\gamma$. There is a constant $K$, depending only on $C,r,v,\lambda,\gamma,\widehat\gamma$, such that for every mesh $\Delta\in(0,1]$ and every integer $i\ge1$, the increment $\Delta_iX=X_{i\Delta}-X_{(i-1)\Delta}$ has a finite second moment and
--   $$\mathbb E\big(|\Delta_iX|^2\,\big|\,\mathcal F_{(i-1)\Delta}\big)\le K\Delta\qquad\text{a.s.}$$
--
--   This is the basic size estimate of an increment over one sampling interval; it yields the bound (8.14) on the local volatility estimators.
--
--   **Formalization Note** $K$ is chosen before the probability space, the model and the mesh, so it is uniform over them, as the paper's convention on constants requires (p. 25). The mesh is restricted to $\Delta\le1$ (the paper's regime $\Delta_n\to0$), because the localized bound used here does not bound $|X_t|$ (see `JacodTodorov10.LLN.Local`) and the drift then contributes $C^2\Delta^2$. Integrability is part of the conclusion, so the conditional expectation is never a junk value.
-- source:
--   Jacod, Todorov, Do price and volatility jump together?, arXiv:1010.4990v1 (Ann. Appl. Probab. 20 (2010)), §8.2, (8.11), p. 28; constants convention p. 25

import Mathlib
import Definitions.Def_JacodTodorov10_LLN_Local

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace JacodTodorov10.LLN

/-- **(8.11)** of Jacod–Todorov, *Do price and volatility jump together?*, arXiv:1010.4990v1
(Ann. Appl. Probab. 20 (2010)), §8.2, p. 28: under (H-r), (K-v) and the localized bound (8.3) with
constant `C`, there is a constant `K`, depending only on `C`, `r`, `v`, `λ`, `γ`, `γ̂` (p. 25: "K is a
constant which … may depend on C above and also on r, v, ϖ and on the function γ"), such that for
every mesh `Δ ∈ (0, 1]` and every `i ≥ 1`, `|Δ_i X|²` is integrable and
`E(|Δ_i X|² | 𝓕_{(i−1)Δ}) ≤ KΔ`.

Formalization Note: the constant is chosen before the probability space, the model and the mesh,
so it is uniform over all of them. The mesh is restricted to `Δ ≤ 1` (the paper's `Δ_n → 0`): the
localized bound `Bdd83` does not bound `|X_t|` (see its note), and without that bound the drift
contributes `C²Δ²` to the left side, which is not `O(Δ)` for large `Δ`. The integrability of `|Δ_i X|²` is part of the conclusion, so the
conditional expectation is not a junk value. -/
theorem eq_8_11 {E : Type*} [MeasurableSpace E] (lam : Measure E) [SigmaFinite lam]
    (r v C : ℝ) (γ γhat : E → ℝ) :
    ∃ K : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (M : Data Ω E) (Γ : ℝ≥0 → Ω → ℝ),
      IsModel 𝓕 P lam M → HAssume 𝓕 P lam r M → KAssume 𝓕 P lam v M →
      Bdd83 lam M r v C Γ γ γhat →
      ∀ Δ : ℝ, 0 < Δ → Δ ≤ 1 → ∀ i : ℕ, 1 ≤ i →
        Integrable (fun ω => incr Δ M.X i ω ^ 2) P ∧
        P[fun ω => incr Δ M.X i ω ^ 2 | 𝓕 (Real.toNNReal (((i : ℝ) - 1) * Δ))]
          ≤ᵐ[P] fun _ => K * Δ := by sorry

end JacodTodorov10.LLN
