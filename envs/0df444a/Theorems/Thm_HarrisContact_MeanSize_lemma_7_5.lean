-- Prove2me | Theorems.Thm_HarrisContact_MeanSize_lemma_7_5
-- name    : HarrisContact.MeanSize.lemma_7_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:27:14.633115+00:00
-- url     : https://prove2.me/theorems/cf29295a-1261-4abb-9500-a03bf996c288
-- title:
--   Lemma 7.5, p. 981 — if $\int_0^\infty m_t\,dt=\infty$ then $\int_0^\infty (m_t(\xi)-m_t)\,dt=\infty$ for $|\xi|\ge2$
-- statement:
--   Let $(\xi_t)$ be a contact process on $Z_d$ with death rate $\mu\ge0$ and non-decreasing birth rates $\lambda_0=0\le\lambda_1\le\dots\le\lambda_{2d}$. Write $m_t=m_t(\{x\})$ for the expected size started from one site (it does not depend on $x$). If
--   $$\int_0^\infty m_t\,dt=\infty,$$
--   then for every finite $\xi$ with $|\xi|\ge2$,
--   $$\int_0^\infty\big(m_t(\xi)-m_t\big)\,dt=\infty .$$
--
--   In the proof of Theorem 7.6 this lemma turns the uniform bound on $M_2(T)-M_1(T)$ into finiteness of $\int_0^\infty m_t\,dt$. The paper omits its proof, saying it is "rather like that of Lemma 5.9".
--
--   **Formalization Note** The standing hypotheses of the contact process (Harris, §2(b), p. 971; §3, p. 972) are written as binders: $d \ge 1$, $\mu \ge 0$, $\lambda_0 = 0$ and $\lambda_k \ge 0$ for $0 \le k \le 2d$. Rates $\lambda_k$ with $k > 2d$ never enter the model, and no hypothesis mentions them. The process is the countable-state chain on finite configurations of §4 (p. 975), with transition function the minimal solution $P_t$ of the backward equations for the rates (4.4)–(4.5); $m_t(\xi)=\sum_\eta P_t(\xi,\eta)\,|\eta|$ is an extended nonnegative real, so a divergent sum is $+\infty$, never $0$. The difference $m_t(\xi)-m_t$ is the truncated subtraction of $[0,\infty]$; since $\lambda_k\uparrow$ makes $m_t$ increasing in the initial set and the process is translation invariant, $m_t(\xi)\ge m_t$ whenever $|\xi|\ge1$, so the truncation changes nothing. The paper assumes nothing about $\mu$ here, and no hypothesis $\mu>0$ is added.
-- source:
--   Harris (Ann. Probab. 2, 1974), Lemma 7.5, p. 981 (proof omitted, p. 982)

import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HarrisContact.MeanSize

/-- Harris (Ann. Probab. 2, 1974), Lemma 7.5, p. 981: if `λ_k ↑` and `∫_0^∞ m_t dt = ∞`, where `m_t` is
`m_t({x})`, then `∫_0^∞ (m_t(ξ) − m_t) dt = ∞` for every `ξ` with `|ξ| ≥ 2`. -/
theorem lemma_7_5 {d : ℕ} (hd : 1 ≤ d) (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ) (h0 : lam 0 = 0)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k)
    (hmono : MonotoneOn lam (Set.Iic (2 * d))) (x : HarrisContact.Extinction.Site d)
    (hinf : ∫⁻ t in Set.Ioi (0 : ℝ), HarrisContact.Extinction.meanSize μ lam t {x} = ∞) :
    ∀ ξ : HarrisContact.Extinction.Config d, 2 ≤ ξ.card →
      ∫⁻ t in Set.Ioi (0 : ℝ), (HarrisContact.Extinction.meanSize μ lam t ξ - HarrisContact.Extinction.meanSize μ lam t {x}) = ∞ := by sorry
end HarrisContact.MeanSize
