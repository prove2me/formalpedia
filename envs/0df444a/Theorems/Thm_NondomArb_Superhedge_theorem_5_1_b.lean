-- Prove2me | Theorems.Thm_NondomArb_Superhedge_theorem_5_1_b
-- name    : NondomArb.Superhedge.theorem_5_1_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:23:55.763395+00:00
-- url     : https://prove2.me/theorems/27777b41-4b64-49bb-baaa-069c9b061ec7
-- title:
--   Theorem 5.1(b) — superhedging theorem with options: π(f) = sup_{Q∈𝒬_φ} E_Q[f] ∈ (−∞, ∞], and an optimal (H, h) exists
-- statement:
--   Consider the nondominated multi-period market of §1.2: a Polish space $\Omega_1$, $\Omega=\Omega_1^T$, random sets $\mathcal P_t(\omega)\subseteq\mathfrak P(\Omega_1)$ (nonempty, convex, with analytic graph) generating the set $\mathcal P$ of models, Borel stock prices $S_t$, $e$ Borel options $g^1,\dots,g^e$ traded statically at price $0$, and semistatic strategies $(H,h)\in\mathcal H\times\mathbb R^e$ with terminal value $H\bullet S_T+hg$. For a random variable $\varphi\ge1$ let $\mathcal Q_\varphi=\{Q\in\mathcal Q: E_Q[\varphi]<\infty\}$, where $\mathcal Q$ is the set (1.3) of martingale measures $Q\lll\mathcal P$ with $E_Q[g^i]=0$.
--
--   **Theorem.** Let $\varphi\ge1$ be a random variable and suppose that $|g^i|\le\varphi$ for $i=1,\dots,e$. Let NA($\mathcal P$) hold, and let $f:\Omega\to\mathbb R$ be an upper semianalytic function such that $|f|\le\varphi$. Then
--   $$\pi(f):=\inf\{x\in\mathbb R:\ \exists(H,h)\in\mathcal H\times\mathbb R^e,\ x+H\bullet S_T+hg\ge f\ \ \mathcal P\text{-q.s.}\}$$
--   satisfies
--   $$\pi(f)=\sup_{Q\in\mathcal Q_\varphi}E_Q[f]\in(-\infty,\infty],$$
--   and there exist $(H,h)\in\mathcal H\times\mathbb R^e$ such that $\pi(f)+H\bullet S_T+hg\ge f$ $\mathcal P$-q.s.
--
--   This is the main result of the paper: under model uncertainty and with statically traded options, the minimal superhedging price is the supremum of the claim's expectations over the martingale measures consistent with the option prices, and it is attained by an optimal semistatic strategy.
--
--   **Formalization Note** $\pi(f)$ is an infimum in `EReal` ($\inf\emptyset=+\infty$), the supremum is an `EReal` supremum of extended expectations (1.1), "$\in(-\infty,\infty]$" is stated as $\bot<\pi(f)$, and the superhedging inequality is in `EReal`. $\varphi$ is a real, universally measurable function.
-- source:
--   Bouchard, Nutz, Arbitrage and duality in nondominated discrete-time models, arXiv:1305.6008v3, p. 30, Theorem 5.1(b)

import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_Measurability
import Definitions.Def_NondomArb_Superhedge_Basic
import Definitions.Def_NondomArb_Superhedge_Model
open MeasureTheory BertsekasShreve.AnalyticSelection

namespace NondomArb.Superhedge

/-- **Theorem 5.1(b)** (p. 30). Superhedging theorem with options: for a random variable `φ ≥ 1`
with `|gⁱ| ≤ φ`, under NA(𝒫) and for `f` upper semianalytic with `|f| ≤ φ`,
`π(f) = sup_{Q ∈ 𝒬_φ} E_Q[f] ∈ (−∞, ∞]`, and some `(H, h) ∈ ℋ × ℝ^e` satisfies
`π(f) + H • S_T + hg ≥ f` `𝒫`-q.s. -/
theorem theorem_5_1_b {Ω₁ : Type*} [TopologicalSpace Ω₁] [PolishSpace Ω₁]
    [MeasurableSpace Ω₁] [BorelSpace Ω₁] {T d : ℕ} {e : ℕ}
    (M : Market Ω₁ T d e) (hM : M.Standing)
    (φ : (Fin T → Ω₁) → ℝ) (hφ : IsUMeasurable φ) (hφ1 : ∀ ω, 1 ≤ φ ω)
    (hgφ : ∀ ω (i : Fin e), |M.g ω i| ≤ φ ω)
    (hNA : M.NA) (f : (Fin T → Ω₁) → ℝ) (hf : IsUpperSemianalytic (fun ω => (f ω : EReal)))
    (hfφ : ∀ ω, |f ω| ≤ φ ω) :
    M.price f = (⨆ Q ∈ M.MartMeasuresWeighted φ, extExp Q (fun ω => (f ω : EReal))) ∧
      ⊥ < M.price f ∧
      ∃ H, M.Admissible H ∧ ∃ h : Fin e → ℝ,
        M.QS (fun ω => (f ω : EReal) ≤ M.price f + ((M.wealth H ω + h ⬝ᵥ M.g ω : ℝ) : EReal)) := by sorry

end NondomArb.Superhedge
