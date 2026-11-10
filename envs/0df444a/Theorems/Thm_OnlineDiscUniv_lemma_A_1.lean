-- Prove2me | Theorems.Thm_OnlineDiscUniv_lemma_A_1
-- name    : OnlineDiscUniv.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:12:55.242366+00:00
-- url     : https://prove2.me/theorems/f299dcec-7371-4b41-afb1-aff905bfa7a7
-- title:
--   Lemma A.1 — projection onto the Brownian filtration preserves a closed convex terminal constraint and lowers $\mathbb E a_t^2$
-- statement:
--   Let $B$ be a Brownian motion in a filtration $\mathbb G=(\mathcal G_t)_{0\le t\le1}$, and let $a$ be $\mathbb G$-progressively measurable with $\mathbb E\int_0^1a_t^2\,dt<\infty$. Let $C\subset\mathbb R$ be closed and convex with
--   $$
--   B_1+\int_0^1a_t\,dt\in C\quad\text{a.s.}\qquad(A.1)
--   $$
--   Let $\mathcal F^B$ be the completed natural filtration of $B$ and $u$ the projection of $a$ onto the $\mathcal F^B$-predictable processes, so that $u_t=\mathbb E[a_t\mid\mathcal F^B_t]$ for a.e. $t$. Then
--   $$
--   B_1+\int_0^1u_t\,dt=\mathbb E\Big[B_1+\int_0^1a_t\,dt\ \Big|\ \mathcal F^B_1\Big]\in C\ \ \text{a.s.},\qquad(A.2)
--   $$
--   and $\mathbb E u_t^2\le\mathbb E a_t^2$ for a.e. $t$ (A.3).
--
--   The lemma lets a control in a larger filtration be replaced by one in the Brownian filtration without losing feasibility or budget; it is used in Propositions 2.1, 4.2 and 5.2.
--
--   Differences from the source:
--   - reading: u the orthogonal projection of a in L²(dt⊗P) onto the F^B-predictable processes, which satisfies u_t = E[a_t | F^B_t] for a.e. t → u any F^B-progressively measurable process with u_t = E[a_t | F^B_t] P-a.s. for a.e. t ∈ [0,1]; reason: the paper identifies the projection by this property; every such u equals the projection dt⊗P-a.e.
--   - encoding: B a Brownian motion in G = (G_t)_{0≤t≤1}; E∫₀¹ a_t² dt < ∞ → ABPOnline.IsBrownianWrt G B P (published: IsBrownianOn1 B P, adapted on [0,1], future increments independent of G_t) for a filtration indexed by ℝ≥0; the iterated lower integral is < ⊤; reason: the published definition is exactly a G-Brownian motion on [0,1]; same instances
-- source:
--   Jo, Lee, Exact Universality of Online Discrepancy, arXiv:2610.00103 (artifact sha256 cb190f127dea2c038b4a22a4787862f82356a983593dfdc3dc3fe3c7c8264ad5), Lemma A.1, p.29 (PDF p.30)

import Mathlib
import Definitions.Def_ABPOnline_Estar
import Definitions.Def_ABPOnline_IsBrownianWrt
import Definitions.Def_OnlineDiscUniv_IsProgOn

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
open ABPOnline (brownFiltration ctrlTerminal secondMoment IsBrownianWrt)

namespace OnlineDiscUniv

/-- **Lemma A.1** (Jo–Lee, arXiv:2610.00103, artifact sha256 cb190f12…, printed p.29, PDF p.30).
Let `B` be a Brownian motion in a filtration `G = (G_t)_{0≤t≤1}`, and let `a` be progressively
measurable with respect to `G`, with `E ∫_0^1 a_t² dt < ∞`. Let `C ⊂ ℝ` be closed and convex and
suppose `B_1 + ∫_0^1 a_t dt ∈ C` a.s. (A.1). Let `u` be the projection of `a` onto the
`F^B`-predictable processes, so that `u_t = E[a_t | F^B_t]` for a.e. `t`. Then
`B_1 + ∫_0^1 u_t dt = E[B_1 + ∫_0^1 a_t dt | F^B_1] ∈ C` a.s. (A.2), and `E u_t² ≤ E a_t²` for a.e.
`t` (A.3).

**Formalization Note** "Brownian motion in `G`" is the published `ABPOnline.IsBrownianWrt`
(standard on `[0,1]`, adapted, future increments independent of `G_t`); `F^B` is the completed
natural filtration of `B` (`ABPOnline.brownFiltration`). The projection `u` is
taken as an `F^B`-progressively measurable process with `u_t = E[a_t | F^B_t]` `P`-a.s. for a.e.
`t ∈ [0,1]`, which is the property of the projection that the paper states. `E ∫_0^1 a_t² dt` is
an iterated lower integral. -/
theorem lemma_A_1 {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : Filtration ℝ≥0 mΩ) (B a : ℝ≥0 → Ω → ℝ) (hB : IsBrownianWrt G B P)
    (ha : IsProgOn G 1 a)
    (ha2 : ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) 1, ‖a t.toNNReal ω‖ₑ ^ 2) ∂P < ⊤)
    (C : Set ℝ) (hCc : IsClosed C) (hCv : Convex ℝ C)
    (hterm : ∀ᵐ ω ∂P, ctrlTerminal B a 1 ω ∈ C) (u : ℝ≥0 → Ω → ℝ)
    (hu : IsProgOn (brownFiltration P B) 1 u)
    (hver : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      u t.toNNReal =ᵐ[P] P[a t.toNNReal | brownFiltration P B t.toNNReal]) :
    ctrlTerminal B u 1 =ᵐ[P] P[ctrlTerminal B a 1 | brownFiltration P B 1] ∧
    (∀ᵐ ω ∂P, ctrlTerminal B u 1 ω ∈ C) ∧
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), secondMoment P u t ≤ secondMoment P a t := by sorry

end OnlineDiscUniv
