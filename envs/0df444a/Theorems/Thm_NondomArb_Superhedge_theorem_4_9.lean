-- Prove2me | Theorems.Thm_NondomArb_Superhedge_theorem_4_9
-- name    : NondomArb.Superhedge.theorem_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:23:42.082337+00:00
-- url     : https://prove2.me/theorems/173dab9f-ba36-4bf6-8e3c-8213d8786e4e
-- title:
--   Theorem 4.9 — without options, sup_{Q∈𝒬_φ} E_Q[f] equals the superhedging price π(f)
-- statement:
--   Consider the multi-period market of §1.2 without options ($e=0$), with $\mathcal Q_\varphi=\{Q\in\mathcal Q:E_Q[\varphi]<\infty\}$.
--
--   **Theorem.** Let NA($\mathcal P$) hold, let $\varphi\ge1$ be a random variable and let $f:\Omega\to\mathbb R$ be an upper semianalytic function such that $|f|\le\varphi$. Then
--   $$\sup_{Q\in\mathcal Q_\varphi}E_Q[f]=\pi(f):=\inf\{x\in\mathbb R:\ \exists H\in\mathcal H,\ x+H\bullet S_T\ge f\ \ \mathcal P\text{-q.s.}\}.$$
--
--   This is the superhedging duality in the nondominated multi-period market when only stocks are traded; it is the base case of the induction over options in Theorem 5.1.
--
--   **Formalization Note** $E_Q[f]$ is the extended expectation (1.1); both sides are computed in `EReal`.
-- source:
--   Bouchard, Nutz, Arbitrage and duality in nondominated discrete-time models, arXiv:1305.6008v3, p. 25, Theorem 4.9

import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_Measurability
import Definitions.Def_NondomArb_Superhedge_Basic
import Definitions.Def_NondomArb_Superhedge_Model
open MeasureTheory BertsekasShreve.AnalyticSelection

namespace NondomArb.Superhedge

/-- **Theorem 4.9** (p. 25). (No options, `e = 0`.) Under NA(𝒫), for `f` upper semianalytic with
`|f| ≤ φ` for a random variable `φ ≥ 1`: `sup_{Q ∈ 𝒬_φ} E_Q[f] = π(f)`. -/
theorem theorem_4_9 {Ω₁ : Type*} [TopologicalSpace Ω₁] [PolishSpace Ω₁]
    [MeasurableSpace Ω₁] [BorelSpace Ω₁] {T d : ℕ}
    (M : Market Ω₁ T d 0) (hM : M.Standing) (hNA : M.NA)
    (φ : (Fin T → Ω₁) → ℝ) (hφ : IsUMeasurable φ) (hφ1 : ∀ ω, 1 ≤ φ ω)
    (f : (Fin T → Ω₁) → ℝ) (hf : IsUpperSemianalytic (fun ω => (f ω : EReal)))
    (hfφ : ∀ ω, |f ω| ≤ φ ω) :
    (⨆ Q ∈ M.MartMeasuresWeighted φ, extExp Q (fun ω => (f ω : EReal))) = M.price f := by sorry

end NondomArb.Superhedge
