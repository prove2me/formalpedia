-- Prove2me | Theorems.Thm_ModelRiskOT_Duality_lemma_16
-- name    : ModelRiskOT.Duality.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T17:15:53.72798+00:00
-- url     : https://prove2.me/theorems/d70210c2-e0d3-47bc-8ba2-890ec8fe1867
-- title:
--   Lemma 16 — $\liminf_n\sup_{y\in S_n}\{f(y)-\lambda_nc(x,y)\}\ge\sup_{y\in\cup_nS_n}\{f(y)-\lambda^*c(x,y)\}$
-- statement:
--   Let $S$ be a Polish space, $c$ a cost satisfying (A1) and $f:S\to\mathbb R$ upper semicontinuous. Let $S_1\subseteq S_2\subseteq\cdots$ be an increasing sequence of subsets of $S$ and $(\lambda_n)$ a real sequence with $\lambda_n\to\lambda^*$ for some $\lambda^*\ge0$. Then for every $x\in S$,
--
--   $$\liminf_{n\to\infty}\ \sup_{y\in S_n}\{f(y)-\lambda_nc(x,y)\}\ \ge\ \sup_{y\in\bigcup_nS_n}\{f(y)-\lambda^*c(x,y)\},$$
--
--   both sides in $[-\infty,\infty]$.
--
--   Lemma 16 is the pointwise inequality behind the Fatou step at the end of the proof of Proposition 7.
--
--   **Formalization Note** Sequences are indexed by $\mathbb N=\{0,1,\dots\}$ instead of $n\ge1$, which does not change the $\liminf$. The paper assumes (A1) and (A2); the integrability part of (A2) refers to a measure that does not appear in the statement and is not assumed.
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 42, Appendix B.3, Lemma 16

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_AssumptionA1
import Definitions.Def_ModelRiskOT_Duality_phiLam

open Filter Topology

namespace ModelRiskOT.Duality

/-- **Lemma 16** (Blanchet & Murthy, arXiv:1604.01446v2, App. B.3, p. 42). Under (A1), with `f`
upper semicontinuous: let `(S_n)` be an increasing sequence of subsets of `S` and `(λ_n)` a real
sequence with `λ_n → λ* ≥ 0`. Then for every `x ∈ S`,
`liminf_n sup_{y ∈ S_n} {f(y) − λ_n c(x, y)} ≥ sup_{y ∈ ⋃_n S_n} {f(y) − λ* c(x, y)}`. -/
theorem lemma_16 {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S] [BorelSpace S]
    (c : S → S → ℝ) (hc : AssumptionA1 c) (f : S → ℝ) (hf_usc : UpperSemicontinuous f)
    (Sn : ℕ → Set S) (hSn : Monotone Sn) (lams : ℕ → ℝ) (lamStar : ℝ)
    (hlim : Tendsto lams atTop (𝓝 lamStar)) (hlamStar : 0 ≤ lamStar) (x : S) :
    phiLamOn c f lamStar (⋃ n, Sn n) x ≤
      liminf (fun n => phiLamOn c f (lams n) (Sn n) x) atTop := by sorry

end ModelRiskOT.Duality
