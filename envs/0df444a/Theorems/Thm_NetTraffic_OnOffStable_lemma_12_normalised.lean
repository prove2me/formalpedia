-- Prove2me | Theorems.Thm_NetTraffic_OnOffStable_lemma_12_normalised
-- name    : NetTraffic.OnOffStable.lemma_12_normalised
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:15:33.565175+00:00
-- url     : https://prove2.me/theorems/a95718ee-4ea7-4b32-b529-0765d31e019a
-- title:
--   Lemma 12 (normalisation restored), p. 53 — b(MT)⁻¹[b₁A₂₁(Tt₁) + b₂(A₂₁(Tt₂) − A₂₁(Tt₁))] → b₁cX(t₁) + b₂(cX(t₂) − cX(t₁))
-- statement:
--   Under (2.1)–(2.2) and Slow Growth Condition 1, with $M=M(T)$ independent stationary ON/OFF sources, write $A_{21}(s)=\sum_{m=1}^M\sum_{k=1}^{\xi^{(m)}_s}J^{(m)}_k$ (with $M=M(T)$ fixed). Let $b_1,b_2\in\mathbb R$ and $t_2\ge t_1\ge0$. Then, as $T\to\infty$,
--   $$[b(MT)]^{-1}\Bigl(b_1A_{21}(Tt_1)+b_2\bigl(A_{21}(Tt_2)-A_{21}(Tt_1)\bigr)\Bigr)\xrightarrow{d}b_1c\,X_{\alpha,\sigma,1}(t_1)+b_2\bigl(c\,X_{\alpha,\sigma,1}(t_2)-c\,X_{\alpha,\sigma,1}(t_1)\bigr),$$
--   with $c$, $\sigma$ as in Theorem 2.
--
--   By the Cramér–Wold device this gives the two-dimensional distributions of Theorem 2.
--
--   **Correction.** The page omits the normalisation $[b(MT)]^{-1}$ on the left-hand side. Without it the left-hand side does not converge (its scale grows like $b(MT)\to\infty$); the proof on p. 53 defines $S_{T,m}$ with the factor $[b(MT)]^{-1}$, and Theorem 2 uses the normalised form. The statement here restores it.
--
--   **Formalization Note.** The limit is the law $\nu$ on $\mathbb R$ with characteristic function $\theta\mapsto\varphi_1(cb_1\theta)\,\varphi_2(cb_2\theta)$, where $\varphi_1$, $\varphi_2$ are the characteristic functions of $S_\alpha(\sigma t_1^{1/\alpha},1,0)$ and $S_\alpha(\sigma(t_2-t_1)^{1/\alpha},1,0)$, the laws of the independent pieces $X(t_1)$ and $X(t_2)-X(t_1)$. The statement asserts that such $\nu$ exists and that the laws converge weakly to it.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 53, Lemma 12 (normalisation [b(MT)]⁻¹ restored, as in its proof)

import Mathlib
import Definitions.Def_NetTraffic_OnOffStable_Setting

namespace NetTraffic.OnOffStable

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics

theorem lemma_12_normalised
    {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon] [IsProbabilityMeasure Foff]
    {α αoff : ℝ} (hF : HeavyTails Fon Foff α αoff)
    {M : ℝ → ℕ} (hM : SourceCount M) (hC1 : Condition1 Fon M)
    {Ω : ℝ → Type*} [∀ T, MeasurableSpace (Ω T)] (P : ∀ T, Measure (Ω T))
    [∀ T, IsProbabilityMeasure (P T)] (src : ∀ T, ℕ → Source (Ω T))
    (hsrc : ∀ T, IsOnOffSuperposition (P T) Fon Foff (M T) (src T))
    (b₁ b₂ t₁ t₂ : ℝ) (ht₁ : 0 ≤ t₁) (ht₁₂ : t₁ ≤ t₂) :
    ∃ ν : ProbabilityMeasure ℝ,
      (∀ θ : ℝ, charFun (ν : Measure ℝ) θ =
        NetTraffic.PoissonStable.stableCharFun α (NetTraffic.PoissonStable.sigmaConst α * t₁ ^ (1 / α)) 1 0 (cConst Fon Foff α * b₁ * θ) *
          NetTraffic.PoissonStable.stableCharFun α (NetTraffic.PoissonStable.sigmaConst α * (t₂ - t₁) ^ (1 / α)) 1 0
            (cConst Fon Foff α * b₂ * θ)) ∧
      NetTraffic.PoissonStable.TendstoInLaw P (fun T ω =>
        (b₁ * A21 Fon Foff (M T) (src T) (T * t₁) ω +
          b₂ * (A21 Fon Foff (M T) (src T) (T * t₂) ω -
            A21 Fon Foff (M T) (src T) (T * t₁) ω)) / NetTraffic.PoissonStable.b Fon ((M T : ℝ) * T)) ν := by sorry

end NetTraffic.OnOffStable
