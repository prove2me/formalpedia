-- Prove2me | Theorems.Thm_FoundationsRL_OnlineLearning_proposition_2
-- name    : FoundationsRL.OnlineLearning.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:19:03.481029+00:00
-- url     : https://prove2.me/theorems/2d188bbb-f17e-4aa5-bd20-afb280f1c479
-- title:
--   Proposition 2 — online-to-batch conversion: $\mathbb E[\mathcal E(\hat f)]\le\frac1T\mathbb E[\mathbf{Reg}]$
-- statement:
--   Let the examples $(x^1,y^1),\dots,(x^T,y^T)$, $T\ge1$, be drawn i.i.d. from a distribution $M^\star$ on $\mathcal X\times\mathcal Y$, and let the prediction set $\mathcal Y'$ be a convex subset of a real vector space on which $a\mapsto\ell(a,b)$ is convex for all $b$. Let $\mathcal F$ be a nonempty class of functions $\mathcal X\to\mathcal Y'$ with integrable losses. Then for any online learning algorithm, the average $\hat f(x)=\frac1T\sum_{t=1}^T\hat f^t(x)$ satisfies
--   $$
--   \mathbb E\big[\mathcal E(\hat f)\big]\le\frac1T\,\mathbb E[\mathbf{Reg}].
--   $$
--
--   This is the sense in which regret generalizes excess risk: a low-regret online algorithm yields a low-excess-risk batch predictor.
--
--   **Formalization Note** The algorithm is a family $\hat f^t:\Omega\times\mathcal X\to\mathcal Y'$. That $\hat f^t$ is computed before the example $(x^t,y^t)$ is seen is expressed by a $\sigma$-algebra $\mathcal G_t$ independent of $(x^t,y^t)$ in which the loss of $\hat f^t$ is measurable. Integrability hypotheses make the expectations genuine.
--
--   Differences from the source:
--   - generalization: an online learning algorithm, f̂^t a function of H^{t−1} → a family fhat t : Ω → X → V with loss jointly measurable in a σ-algebra 𝓖 t independent of Z t; reason: 𝓖 t = σ(Z 0, …, Z (t−1)) is the deterministic algorithm of the notes, and adding internal randomness gives the randomized algorithms of Remark 4
--   - reading: Y′ not stated to be convex → Yp a convex subset of a real vector space V; reason: the average f̂ must be a prediction; p. 15 says averaging is only applicable when Y′ is convex
--   - encoding: min_{f∈F} in Reg and in E(f), expectations → real infimum, with hbdd, hReg and the integrability hypotheses; reason: the notes assume these objects exist; without such hypotheses Lean’s infimum and Bochner integral would be 0
--   - encoding: rounds t = 1, …, T → 0-based rounds in Finset.range T; reason: Lean convention; same instances
--   - encoding: min_{f∈F} and 1/T presupposed → F.Nonempty and 0 < T; reason: the minimum over F and the average with 1/T are undefined otherwise; no instance of the notes is excluded
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Proposition 2, p. 14; proof (1.20)–(1.22), p. 14

import Mathlib
import Definitions.Def_FoundationsRL_OnlineLearning_Protocol
import Definitions.Def_FoundationsRL_OnlineLearning_ExcessRisk

open MeasureTheory ProbabilityTheory

namespace FoundationsRL.OnlineLearning

/-- **Proposition 2 (online-to-batch conversion).** Foster & Rakhlin, Foundations of Reinforcement
Learning and Interactive Decision Making, arXiv:2312.16730v1, Proposition 2, p. 14.

If the examples `Z t = (x^t, y^t)` are i.i.d. with law `Mstar` and `a ↦ ℓ(a, b)` is convex on the
convex prediction set `Yp` for all `b`, then for any online learning algorithm
`f̂(x) = (1/T) ∑_{t=1}^T f̂^t(x)` satisfies `E[E(f̂)] ≤ (1/T) E[Reg]`.

**Formalization Note.** The algorithm is a family `fhat t : Ω → X → V`. That `f̂^t` is computed before
`(x^t, y^t)` is seen is the pair `h𝓖Z`, `hfhatm`: the loss of `f̂^t` is jointly measurable in a
σ-algebra `𝓖 t` independent of `Z t`. A deterministic algorithm has `𝓖 t = σ(Z 0, …, Z (t-1))`, and a
randomized one also puts its internal randomness in `𝓖 t`. `hbdd` and `hReg` make the infimum in `Reg`
and the expectation `E[Reg]` genuine (the notes write `min` and do not discuss measurability). The
integrability hypotheses make the expectations genuine; they hold, for example, for bounded losses. -/
theorem proposition_2 {X Y V Ω : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [AddCommGroup V] [Module ℝ V] [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Mstar : Measure (X × Y)) [IsProbabilityMeasure Mstar]
    (Yp : Set V) (hYp : Convex ℝ Yp) (ℓ : V → Y → ℝ) (hℓ : ∀ b, ConvexOn ℝ Yp fun a => ℓ a b)
    (F : Set (X → V)) (hF : F.Nonempty) (hFYp : ∀ f ∈ F, ∀ x, f x ∈ Yp)
    (hFint : ∀ f ∈ F, Integrable (fun z : X × Y => ℓ (f z.1) z.2) Mstar)
    (T : ℕ) (hT : 0 < T)
    (Z : ℕ → Ω → X × Y) (hZ : ∀ t, Measurable (Z t)) (hZlaw : ∀ t, P.map (Z t) = Mstar)
    (hZindep : iIndepFun Z P)
    (𝓖 : ℕ → MeasurableSpace Ω) (h𝓖 : ∀ t, 𝓖 t ≤ mΩ)
    (h𝓖Z : ∀ t, Indep (𝓖 t) (MeasurableSpace.comap (Z t) inferInstance) P)
    (fhat : ℕ → Ω → X → V) (hfhatYp : ∀ t < T, ∀ ω x, fhat t ω x ∈ Yp)
    (hfhatm : ∀ t < T, Measurable[(𝓖 t).prod inferInstance]
      fun p : Ω × (X × Y) => ℓ (fhat t p.1 p.2.1) p.2.2)
    (hfhatint : ∀ t < T,
      Integrable (fun p : Ω × (X × Y) => ℓ (fhat t p.1 p.2.1) p.2.2) (P.prod Mstar))
    (havgint : Integrable
      (fun p : Ω × (X × Y) => ℓ (onlineAverage T (fun t => fhat t p.1) p.2.1) p.2.2) (P.prod Mstar))
    (hbdd : ∀ᵐ ω ∂P, BddBelow (Set.range fun f : F =>
      cumLoss ℓ (fun _ => (f : X → V)) (fun t => (Z t ω).1) (fun t => (Z t ω).2) T))
    (hReg : Integrable (fun ω =>
      regret ℓ F (fun t => fhat t ω) (fun t => (Z t ω).1) (fun t => (Z t ω).2) T) P) :
    ∫ ω, excessRisk ℓ Mstar F (onlineAverage T fun t => fhat t ω) ∂P ≤
      (1 / T : ℝ) *
        ∫ ω, regret ℓ F (fun t => fhat t ω) (fun t => (Z t ω).1) (fun t => (Z t ω).2) T ∂P := by sorry

end FoundationsRL.OnlineLearning
