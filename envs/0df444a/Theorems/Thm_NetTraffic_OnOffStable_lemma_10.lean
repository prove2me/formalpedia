-- Prove2me | Theorems.Thm_NetTraffic_OnOffStable_lemma_10
-- name    : NetTraffic.OnOffStable.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:15:29.184324+00:00
-- url     : https://prove2.me/theorems/841f62f3-48a2-474d-bc4a-1a2d70344ebe
-- title:
--   Lemma 10, p. 50 — [b(MT)]⁻¹ A₂₁ → c X_{α,σ,1}(1) in distribution
-- statement:
--   Under (2.1)–(2.2) and Slow Growth Condition 1, with $M=M(T)$ independent stationary ON/OFF sources, let
--   $$A_{21}=\sum_{m=1}^M S_{T,m},\qquad S_{T,m}=\sum_{k=1}^{\xi^{(m)}_T}J^{(m)}_k,$$
--   and let $c=\mu_{\mathrm{off}}/\mu^{1+1/\alpha}$, $\sigma=C_\alpha^{-1/\alpha}$, $C_\alpha=(1-\alpha)/(\Gamma(2-\alpha)\cos(\pi\alpha/2))$. Then, as $T\to\infty$,
--   $$[b(MT)]^{-1}A_{21}\xrightarrow{d}c\,X_{\alpha,\sigma,1}(1),$$
--   where $X_{\alpha,\sigma,1}(1)\sim S_\alpha(\sigma,1,0)$.
--
--   This is the one-dimensional stable limit of the main part of the cumulative input; with Lemmas 3 and 6 it gives the one-dimensional case of Theorem 2.
--
--   **Formalization Note.** The limit law is not taken from a library: the statement asserts that there is a probability measure $\nu$ on $\mathbb R$ whose characteristic function is $\theta\mapsto\varphi_{S_\alpha(\sigma,1,0)}(c\theta)$ (the law of $cX_{\alpha,\sigma,1}(1)$), and that the laws of $[b(MT)]^{-1}A_{21}$ converge weakly to $\nu$. The characteristic function determines $\nu$.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 50, Lemma 10

import Mathlib
import Definitions.Def_NetTraffic_OnOffStable_Setting

namespace NetTraffic.OnOffStable

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics

theorem lemma_10
    {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon] [IsProbabilityMeasure Foff]
    {α αoff : ℝ} (hF : HeavyTails Fon Foff α αoff)
    {M : ℝ → ℕ} (hM : SourceCount M) (hC1 : Condition1 Fon M)
    {Ω : ℝ → Type*} [∀ T, MeasurableSpace (Ω T)] (P : ∀ T, Measure (Ω T))
    [∀ T, IsProbabilityMeasure (P T)] (src : ∀ T, ℕ → Source (Ω T))
    (hsrc : ∀ T, IsOnOffSuperposition (P T) Fon Foff (M T) (src T)) :
    ∃ ν : ProbabilityMeasure ℝ,
      (∀ θ : ℝ, charFun (ν : Measure ℝ) θ =
        NetTraffic.PoissonStable.stableCharFun α (NetTraffic.PoissonStable.sigmaConst α) 1 0 (cConst Fon Foff α * θ)) ∧
      NetTraffic.PoissonStable.TendstoInLaw P (fun T ω => A21 Fon Foff (M T) (src T) T ω / NetTraffic.PoissonStable.b Fon ((M T : ℝ) * T)) ν := by sorry

end NetTraffic.OnOffStable
