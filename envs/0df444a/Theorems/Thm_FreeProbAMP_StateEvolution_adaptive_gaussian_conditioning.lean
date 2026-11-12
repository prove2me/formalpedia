-- Prove2me | Theorems.Thm_FreeProbAMP_StateEvolution_adaptive_gaussian_conditioning
-- name    : FreeProbAMP.StateEvolution.adaptive_gaussian_conditioning
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:28:00.060821+00:00
-- url     : https://prove2.me/theorems/53bb517e-279c-4082-b4b8-94019f3d15af
-- title:
--   Lemma 4.1 — adaptive Gaussian conditioning
-- statement:
--   Let $n,d>0$ and let $(q^t,r^t)_{0\le t\le T}$ be an alternating adaptive observation scheme for the GOE operator $A$ with histories $\mathcal F_t,\mathcal G_t$. Suppose $Q_T=(q^0|\cdots|q^T)$ and $R_T=(r^0|\cdots|r^T)$ have full column rank almost surely. Put $Y_T=AQ_T$, $X_T=A^*R_T$, $G_Q=Q_T^*Q_T$, $G_R=R_T^*R_T$, and let $P_Q,P_R$ be the orthogonal range projections. Let $\widetilde A$ be an independent copy, independent of $\sigma(A)\vee\mathcal F_{T+1}$.
--
--   For an $\mathcal F_{T+1}$-measurable query $q=Q_T\beta+h$ with $h\perp\operatorname{Ran}(Q_T)$, conditionally on $\mathcal F_{T+1}$,
--
--   $$Aq\overset d=Y_T\beta+R_TG_R^{-1}X_T^*h+P_R^\perp\widetilde Ah.$$
--
--   For a $\mathcal G_T$-measurable symmetric query $k=R_{T-1}\gamma+\ell$ with $\ell\perp\operatorname{Ran}(R_{T-1})$, conditionally on $\mathcal G_T$,
--
--   $$A^*k\overset d=X_{T-1}\gamma+Q_TG_Q^{-1}Y_T^*\ell+P_Q^\perp\widetilde A^*\ell.$$
--
--   The subscript $T-1$ deletes the final column; at $T=0$ it denotes an empty column map and its contribution is zero. This gives both conditional laws needed for the two AMP half-steps. Adjoints use the normalized source inner products.
--
--   Differences from the source:
--   - encoding: random vectors and matrix observations → explicit measurability of random data and almost-everywhere symmetry; reason: the standing random-variable convention is made explicit; no distribution is excluded
--   - encoding: operators on H_n and K_d → 0 < n and 0 < d; reason: nondegeneracy only; the normalized inner products 1/n and 1/d are undefined at zero
-- source:
--   August Chen, Ahmed El Alaoui, STOC 2027 submission #1182 (October 2026), p. 23, Lemma 4.1, (4.6)–(4.7); setup pp. 22–23

import Mathlib
import Definitions.Def_FreeProbAMP_StateEvolution_History

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal Matrix
set_option autoImplicit false
noncomputable section

namespace FreeProbAMP.StateEvolution

/-- Lemma 4.1, submission p.23, both conditional laws. -/
theorem adaptive_gaussian_conditioning
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n d T : ℕ) (hn : 0 < n) (hd : 0 < d) (O : Observation Ω n d)
    (hg : GOEArray μ O.A) (ha : O.Adaptive μ T)
    (hq : ∀ᵐ ω ∂μ, LinearIndependent ℝ (fun j : Fin (T+1) => O.q j ω))
    (hr : ∀ᵐ ω ∂μ, LinearIndependent ℝ (fun j : Fin (T+1) => O.r j ω))
    (fresh : Ω → Fin n → RMat d) (hf : Measurable fresh)
    (hl : μ.map fresh = μ.map O.A)
    (hi : Indep (sigma fresh) (sigma O.A ⊔ O.F (T+1)) μ)
    (q : Ω → Fin n → ℝ) (β : Ω → Fin (T+1) → ℝ) (h : Ω → Fin n → ℝ)
    (k : Ω → RMat d) (γ : Ω → Fin T → ℝ) (ell : Ω → RMat d)
    (hmq : Measurable[O.F (T+1)] q) (hmk : Measurable[O.G T] k)
    (hmb : Measurable β) (hmh : Measurable h) (hmc : Measurable γ) (hme : Measurable ell)
    (hks : ∀ᵐ ω ∂μ, (k ω).transpose = k ω ∧ (ell ω).transpose = ell ω)
    (hdq : ∀ᵐ ω ∂μ, q ω = columns (fun j : Fin (T+1) => O.q j ω) (β ω) + h ω ∧
      ∀ j : Fin (T+1), vecInner (O.q j ω) (h ω) = 0)
    (hdk : ∀ᵐ ω ∂μ, k ω = columns (fun j : Fin T => O.r j ω) (γ ω) + ell ω ∧
      ∀ j : Fin T, matInner (O.r j ω) (ell ω) = 0) :
    CondSameLaw μ (O.F (T+1)) (fun ω => applyA (O.A ω) (q ω))
      (fun ω =>
        let R := fun j : Fin (T+1) => O.r j ω
        let X := fun j : Fin (T+1) => O.x j ω
        let Y := fun j : Fin (T+1) => O.y j ω
        columns Y (β ω) + columns R ((gram matInner R)⁻¹ *ᵥ adjColumns vecInner X (h ω)) +
          (applyA (fresh ω) (h ω) - spanProjection matInner R (applyA (fresh ω) (h ω)))) ∧
    CondSameLaw μ (O.G T) (fun ω => applyAdj (O.A ω) (k ω))
      (fun ω =>
        let Q := fun j : Fin (T+1) => O.q j ω
        let Y := fun j : Fin (T+1) => O.y j ω
        let Xminus := fun j : Fin T => O.x j ω
        columns Xminus (γ ω) + columns Q ((gram vecInner Q)⁻¹ *ᵥ adjColumns matInner Y (ell ω)) +
          (applyAdj (fresh ω) (ell ω) - spanProjection vecInner Q (applyAdj (fresh ω) (ell ω)))) := by sorry

end FreeProbAMP.StateEvolution
