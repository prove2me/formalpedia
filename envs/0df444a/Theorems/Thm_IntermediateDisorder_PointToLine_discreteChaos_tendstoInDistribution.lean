-- Prove2me | Theorems.Thm_IntermediateDisorder_PointToLine_discreteChaos_tendstoInDistribution
-- name    : IntermediateDisorder.PointToLine.discreteChaos_tendstoInDistribution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:42:34.224624+00:00
-- url     : https://prove2.me/theorems/f3bae140-1d7c-4291-a0b2-08bba71a516b
-- title:
--   Lemma 4.4 — discrete chaos $I^n(g)\to I(g)$ in law, for Fock vectors supported on the simplices
-- statement:
--   Let the environment $\omega$ be i.i.d. with mean zero and variance one, and let $W$ be a white noise on $[0,1]\times\mathbb R$ with multiple stochastic integrals $I=(I_k)$. Let $g=(g_0,g_1,g_2,\dots)$ with $g_k\in L^2([0,1]^k\times\mathbb R^k)$ vanishing outside $\Delta_k\times\mathbb R^k$ and $\sum_k\|g_k\|^2_{L^2}<\infty$. Then $I(g)=\sum_kI_k(g_k)$ converges in $L^2(Q')$ and, as $n\to\infty$,
--
--   $$I^n(g):=\sum_{k=0}^\infty n^{-3k/4}\,\mathcal S_k^n(g_k)\xrightarrow{(d)}\sum_{k=0}^\infty\int_{[0,1]^k}\int_{\mathbb R^k}g_k(\mathbf t,\mathbf x)\,W^{\otimes k}(d\mathbf t\,d\mathbf x)=I(g).$$
--
--   Moreover, if $G_1,\dots,G_m$ are such sequences, then $(I^n(G_1),\dots,I^n(G_m))\xrightarrow{(d)}(I(G_1),\dots,I(G_m))$.
--
--   This is the passage from finitely many chaos orders (Theorem 4.3) to whole chaos expansions; Proposition 5.3 applies it to $\boldsymbol\varrho(\sqrt2\beta)$.
--
--   **Formalization Note** The paper states the lemma for every element of $\bigoplus_kL^2([0,1]^k\times\mathbb R^k)$. Here every $g_k$ is required to vanish outside $\Delta_k\times\mathbb R^k$: for general non-symmetric $g_k$, $\operatorname{Var}I_k(g_k)$ can reach $k!\,\|g_k\|^2$, so $\sum_kI_k(g_k)$ need not converge, and the proof's bound $\operatorname{Var}(n^{-3k/4}\mathcal S_k^n(g_k))\le\operatorname{Var}(I_k(g_k))$ rests on the corrected Lemma 4.1. The sequences used in Section 5 satisfy the restriction. The sum defining $I^n(g)$ is finite: its terms with $k>n$ vanish.
-- source:
--   Alberts, Khanin, Quastel, The intermediate disorder regime for directed polymers in dimension 1+1, arXiv:1202.4398v3, p. 27, Lemma 4.4 (stated for Fock vectors supported on the simplices)

import Mathlib
import Definitions.Def_IntermediateDisorder_PointToLine_Environment
import Definitions.Def_IntermediateDisorder_PointToLine_WienerChaos
import Definitions.Def_IntermediateDisorder_PointToLine_UStatistic

namespace IntermediateDisorder.PointToLine

open MeasureTheory ProbabilityTheory Filter

/-- Lemma 4.4 (for Fock vectors supported on the simplices): if `g = (g_k)` with each `g_k`
vanishing outside `Δ_k × ℝ^k` and `∑_k ‖g_k‖² < ∞`, then `∑_k I_k(g_k)` converges in `L²` and
`I^n(g) = ∑_k n^{-3k/4} 𝒮_k^n(g_k) → I(g)` in distribution; jointly for finitely many such
`G_1, …, G_m`. -/
theorem discreteChaos_tendstoInDistribution {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {ω : ℕ × ℤ → Ω → ℝ} (hω : IsStdEnvironment ω Q)
    {Ω' : Type*} [MeasurableSpace Ω'] {Q' : Measure Ω'} [IsProbabilityMeasure Q']
    (W : Set (ℝ × ℝ) → Ω' → ℝ) (I : (k : ℕ) → Lp ℝ 2 (kernelMeasure k) →L[ℝ] Lp ℝ 2 Q')
    (hW : IsWhiteNoise W Q') (hI : IsMultipleIntegral W Q' I) :
    (∀ g : (k : ℕ) → Lp ℝ 2 (kernelMeasure k),
      (∀ k, SimplexSupported (g k)) → Summable (fun k => ‖g k‖ ^ 2) →
      Summable (fun k => I k (g k)) ∧
      TendstoInDistribution (fun n => (discreteChaos ω Q n g : Ω → ℝ)) atTop
        (fockIntegral I g : Ω' → ℝ) (fun _ => Q) Q') ∧
    (∀ (m : ℕ) (G : Fin m → (k : ℕ) → Lp ℝ 2 (kernelMeasure k)),
      (∀ l k, SimplexSupported (G l k)) → (∀ l, Summable (fun k => ‖G l k‖ ^ 2)) →
      TendstoInDistribution (fun (n : ℕ) a l => (discreteChaos ω Q n (G l) : Ω → ℝ) a) atTop
        (fun b l => (fockIntegral I (G l) : Ω' → ℝ) b) (fun _ => Q) Q') := by sorry

end IntermediateDisorder.PointToLine
