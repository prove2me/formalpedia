-- Prove2me | Theorems.Thm_LocalOccupancyIS_Glauber_Supplement_lemma_14
-- name    : LocalOccupancyIS.Glauber.Supplement.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T22:02:55.227893+00:00
-- url     : https://prove2.me/theorems/f16b7dea-0dec-4354-936d-d4c273e7d8a7
-- title:
--   Lemma 14 — partition and lower-tail estimates
-- statement:
--   Use the appendix parameters $\Delta\ge3$, integer $t\ge1$, $b\ge0$, $L,H,\lambda_A,M_A,c_A$. Assume $H\ge1$ and $H^2\ge8et/(4e)^{1/t}$. Let $F$ be any finite graph on $k$ vertices of $K_{t,t}$-density at most $b$, and let $X=|I|$ for $I\sim\mu_{F,\lambda_A}$. If $k\le M_A$, then
--
--   $$\log Z_F(\lambda_A)\ge c_A\lambda_A k,\qquad \mathbb P(X\le(1-\eta)c_A\lambda_A k)\le\exp(-\eta^2c_A\lambda_A k/2)\quad(0<\eta<1).$$
--
--   If $k>M_A$, then
--
--   $$\mathbb P(X\le L)\le2^{-L}.$$
--
--   These are finite bounds, including $k=0$ and the real cutoff $L$, with no asymptotic assumption or independence assumption on the occupancy indicators. They supply the quantile estimates for chromatic local occupancy.
--
--   Differences from the source: none.
-- source:
--   Ewan Davies, Brian Tan, STOC 2027 submission #982 (October 2026), pp.23–24, Lemma 14, equations (32)–(34)

import Definitions.Def_LocalOccupancyIS_Glauber_Supplement_AppendixParameters

namespace LocalOccupancyIS.Glauber.Supplement
/-- Lemma 14, pp.23–24: a finite statement, including the empty graph. -/
theorem lemma_14 (Δ : ℝ) (t : ℕ) (b : ℝ)
    (hΔ : 3 ≤ Δ) (ht : 1 ≤ t) (hb : 0 ≤ b)
    (hH : 1 ≤ appH Δ t b)
    (hH₂ : 8 * Real.exp 1 * t / (4 * Real.exp 1)^(1/(t : ℝ)) ≤ appH Δ t b ^ 2)
    {V : Type} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (hdensity : Density F t b) :
    let k : ℝ := Fintype.card V
    let lam := appLam Δ t b
    let c := appC Δ t b
    (k ≤ appM Δ t b →
      Real.log (partition F lam) ≥ c * lam * k ∧
      ∀ η : ℝ, 0 < η → η < 1 →
        sizeLE F lam ((1-η)*c*lam*k) ≤ Real.exp (-η^2*c*lam*k/2)) ∧
    (appM Δ t b < k → sizeLE F lam (appL Δ) ≤ (2 : ℝ)^(-appL Δ)) := by sorry
end LocalOccupancyIS.Glauber.Supplement
