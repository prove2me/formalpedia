-- Prove2me | Theorems.Thm_NondomArb_Superhedge_theorem_5_1_a
-- name    : NondomArb.Superhedge.theorem_5_1_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:23:37.886635+00:00
-- url     : https://prove2.me/theorems/191cf49d-1885-4642-8e6a-456885f30e51
-- title:
--   Theorem 5.1(a) — first fundamental theorem with options: NA(𝒫) iff every P ∈ 𝒫 is dominated by some Q ∈ 𝒬_φ
-- statement:
--   Consider the multi-period market of §1.2 with $d$ stocks and $e$ options $g^1,\dots,g^e$ traded statically at price $0$, and $\mathcal Q_\varphi=\{Q\in\mathcal Q: E_Q[\varphi]<\infty\}$ with $\mathcal Q$ as in (1.3).
--
--   **Theorem.** Let $\varphi\ge1$ be a random variable and suppose that $|g^i|\le\varphi$ for $i=1,\dots,e$. The following are equivalent:
--   1. NA($\mathcal P$) holds;
--   2. for all $P\in\mathcal P$ there exists $Q\in\mathcal Q_\varphi$ such that $P\ll Q$.
--
--   This is the paper's First Fundamental Theorem in its precise weighted form.
-- source:
--   Bouchard, Nutz, Arbitrage and duality in nondominated discrete-time models, arXiv:1305.6008v3, p. 30, Theorem 5.1(a)

import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_Measurability
import Definitions.Def_NondomArb_Superhedge_Basic
import Definitions.Def_NondomArb_Superhedge_Model
open MeasureTheory BertsekasShreve.AnalyticSelection

namespace NondomArb.Superhedge

/-- **Theorem 5.1(a)** (p. 30). First fundamental theorem with options: for a random variable
`φ ≥ 1` with `|gⁱ| ≤ φ`, NA(𝒫) holds if and only if every `P ∈ 𝒫` is absolutely continuous with
respect to some `Q ∈ 𝒬_φ`. -/
theorem theorem_5_1_a {Ω₁ : Type*} [TopologicalSpace Ω₁] [PolishSpace Ω₁]
    [MeasurableSpace Ω₁] [BorelSpace Ω₁] {T d : ℕ} {e : ℕ}
    (M : Market Ω₁ T d e) (hM : M.Standing)
    (φ : (Fin T → Ω₁) → ℝ) (hφ : IsUMeasurable φ) (hφ1 : ∀ ω, 1 ≤ φ ω)
    (hgφ : ∀ ω (i : Fin e), |M.g ω i| ≤ φ ω) :
    M.NA ↔ ∀ P ∈ M.models, ∃ Q ∈ M.MartMeasuresWeighted φ, P ≪ Q := by sorry

end NondomArb.Superhedge
