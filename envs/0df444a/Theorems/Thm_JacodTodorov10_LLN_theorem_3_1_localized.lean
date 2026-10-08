-- Prove2me | Theorems.Thm_JacodTodorov10_LLN_theorem_3_1_localized
-- name    : JacodTodorov10.LLN.theorem_3_1_localized
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:21:02.884115+00:00
-- url     : https://prove2.me/theorems/f7b94474-4e2d-4643-95c8-b1aa76f46259
-- title:
--   Theorem 3.1 under the localized bound (8.3) — what §8.4 proves
-- statement:
--   Assume the hypotheses of Theorem 3.1 — (H-$r$) for some $r<2$, (K-$v$), (3.3), $F$ Borel and continuous at each point of $R\times(0,\infty)^2$ for some $R\in\mathcal R$, and one of the cases (a) $F(x,y,z)=0$ for $|x|\le\varepsilon$; (b) $r=0$; (c) $|F(x,y,z)|\le K|x|^r(1+y+z)$ for $|x|\le\varepsilon$ — and in addition the localized bound (8.3) with constant $C$, process $\Gamma$ and functions $\gamma,\widehat\gamma$. Then, almost surely, the series $U(F)_t$ converges absolutely for all $t$, and
--   $$U(F,k_n)\xrightarrow{\ \mathbb P\ }U(F)\qquad\text{for the Skorokhod topology.}$$
--
--   This is the statement §8.4 proves; by the localization procedure of §8.1 it implies Theorem 3.1.
--
--   **Formalization Note** As for Theorem 3.1. The bound (8.3) is used without its term $|X_t|$, which cannot hold together with the other bounds for all $t$ (see `JacodTodorov10.LLN.Local`).
-- source:
--   Jacod, Todorov, Do price and volatility jump together?, arXiv:1010.4990v1 (Ann. Appl. Probab. 20 (2010)), §8.1, pp. 24–25 (localization, (8.3)); §8.4, pp. 33–34; Theorem 3.1, p. 5

import Mathlib
import Definitions.Def_JacodTodorov10_LLN_Local

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace JacodTodorov10.LLN

/-- **Theorem 3.1 under the localized bound (8.3)** — Jacod–Todorov, *Do price and volatility jump
together?*, arXiv:1010.4990v1 (Ann. Appl. Probab. 20 (2010)), §8.1, pp. 24–25 (the localization
paragraph) and §8.4, pp. 33–34. This is what §8.4 proves: the conclusion of Theorem 3.1 (p. 5)
under its hypotheses — (H-r) with `r < 2`, (K-v), (3.3), `F` Borel and continuous on `R × ℝ*₊²` for
some `R ∈ 𝓡`, and one of the cases (a)–(c) — together with the additional assumption (8.3) with
constant `C`, process `Γ` and functions `γ`, `γ̂`. A localization procedure reduces Theorem 3.1 to
this statement.

Formalization Note: as for Theorem 3.1; (8.3) is `Bdd83`, in which the same `Γ` dominates `δ`, `δ̂`
and plays `Γ'` in (2.2) (p. 24). -/
theorem theorem_3_1_localized {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (lam : Measure E) [SigmaFinite lam] (M : Data Ω E) (r v C : ℝ) (Γ : ℝ≥0 → Ω → ℝ)
    (γ γhat : E → ℝ) (S : Scheme) (ϖ ρ : ℝ) (F : ℝ → ℝ → ℝ → ℝ)
    (hM : IsModel 𝓕 P lam M) (hH : HAssume 𝓕 P lam r M) (hr : r < 2)
    (hK : KAssume 𝓕 P lam v M) (hB : Bdd83 lam M r v C Γ γ γhat) (hS : S.Cond33 ϖ ρ)
    (hFmeas : Measurable (fun q : ℝ × ℝ × ℝ => F q.1 q.2.1 q.2.2))
    (hFcont : ∃ R : Set ℝ, InR P M.X R ∧ ∀ x ∈ R, ∀ y z : ℝ, 0 < y → 0 < z →
      ContinuousAt (fun q : ℝ × ℝ × ℝ => F q.1 q.2.1 q.2.2) (x, y, z))
    (hcase : (∃ ε > 0, ∀ x y z : ℝ, |x| ≤ ε → 0 < y → 0 < z → F x y z = 0) ∨ r = 0 ∨
      (∃ ε > 0, ∃ K > 0, ∀ x y z : ℝ, |x| ≤ ε → 0 < y → 0 < z →
        |F x y z| ≤ K * |x| ^ r * (1 + y + z))) :
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Summable (fun s : {s : ℝ≥0 // 0 < s ∧ s ≤ t ∧ pjump M.X s ω ≠ 0} =>
        F (pjump M.X s ω) (cLeft M.σ s ω) (c M.σ s ω))) ∧
    TendstoInProbJ1 P (fun n => UFk S M.X F n) (UF M.X M.σ F) := by sorry

end JacodTodorov10.LLN
