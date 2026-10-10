-- Prove2me | Theorems.Thm_NondomArb_Superhedge_lemma_4_13
-- name    : NondomArb.Superhedge.lemma_4_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:23:24.978791+00:00
-- url     : https://prove2.me/theorems/3ffc6992-90aa-468b-b209-01fc3b97996a
-- title:
--   Lemma 4.13 — for f bounded above, some H gives sup_{Q∈𝒬_φ} E_Q[f] + H • S_T ≥ f 𝒫-q.s.
-- statement:
--   Consider the multi-period market of §1.2 without options ($e=0$). For a random variable $\varphi\ge1$ let $\mathcal Q_\varphi=\{Q\in\mathcal Q: E_Q[\varphi]<\infty\}$.
--
--   **Lemma.** Let NA($\mathcal P$) hold, let $f:\Omega\to\mathbb R$ be upper semianalytic and bounded from above, and let $\varphi\ge1$ be a random variable such that $|f|\le\varphi$. Then there exists $H\in\mathcal H$ such that
--   $$\sup_{Q\in\mathcal Q_\varphi}E_Q[f]+H\bullet S_T\ge f\qquad\mathcal P\text{-q.s.}$$
--
--   This is the hard inequality of the multi-period duality for claims bounded from above.
--
--   **Formalization Note** $\varphi$ is a real, universally measurable function; the supremum is taken in `EReal` and the inequality is in `EReal`.
-- source:
--   Bouchard, Nutz, Arbitrage and duality in nondominated discrete-time models, arXiv:1305.6008v3, p. 28, Lemma 4.13

import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_Measurability
import Definitions.Def_NondomArb_Superhedge_Basic
import Definitions.Def_NondomArb_Superhedge_Model
open MeasureTheory BertsekasShreve.AnalyticSelection

namespace NondomArb.Superhedge

/-- **Lemma 4.13** (p. 28). (No options, `e = 0`.) Under NA(𝒫), for `f` upper semianalytic and
bounded from above with `|f| ≤ φ` for a random variable `φ ≥ 1`, some `H ∈ ℋ` gives
`sup_{Q ∈ 𝒬_φ} E_Q[f] + H • S_T ≥ f` `𝒫`-q.s. -/
theorem lemma_4_13 {Ω₁ : Type*} [TopologicalSpace Ω₁] [PolishSpace Ω₁]
    [MeasurableSpace Ω₁] [BorelSpace Ω₁] {T d : ℕ}
    (M : Market Ω₁ T d 0) (hM : M.Standing) (hNA : M.NA)
    (φ : (Fin T → Ω₁) → ℝ) (hφ : IsUMeasurable φ) (hφ1 : ∀ ω, 1 ≤ φ ω)
    (f : (Fin T → Ω₁) → ℝ) (hf : IsUpperSemianalytic (fun ω => (f ω : EReal)))
    (hfb : BddAbove (Set.range f)) (hfφ : ∀ ω, |f ω| ≤ φ ω) :
    ∃ H, M.Admissible H ∧
      M.QS (fun ω => (f ω : EReal) ≤
        (⨆ Q ∈ M.MartMeasuresWeighted φ, extExp Q (fun ω' => (f ω' : EReal))) +
          ((M.wealth H ω : ℝ) : EReal)) := by sorry

end NondomArb.Superhedge
