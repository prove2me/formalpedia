-- Prove2me | Theorems.Thm_GraphonCheeger_lemma_4_26
-- name    : GraphonCheeger.lemma_4_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:59:56.825779+00:00
-- url     : https://prove2.me/theorems/d6887813-3895-450e-9d49-02b7e5a2b756
-- title:
--   Lemma 4.26: the Cheeger constant, degree function and density are invariant under pullback
-- statement:
--   Let $W$ be a graphon on $(\Omega_2,\mathcal F_2,\mu_2)$ with $\rho_W>0$, and let $\varphi:(\Omega_1,\mathcal F_1,\mu_1)\to(\Omega_2,\mathcal F_2,\mu_2)$ be measure-preserving. With $W^\varphi(x,y)=W(\varphi(x),\varphi(y))$,
--
--   $$h(W^\varphi)=h(W),$$
--
--   and moreover $k_{W^\varphi}=k_W\circ\varphi$ $\mu_1$-a.e. and $\rho_{W^\varphi}=\rho_W$.
--
--   This invariance is what allows two graphons on different spaces to be compared on a common space.
--
--   Differences from the source: none.
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813…), Lemma 4.26, (4.119)–(4.120), p.47

import Mathlib
import Definitions.Def_GraphonCheeger_cheegerW

open MeasureTheory

namespace GraphonCheeger

/-- Lemma 4.26, p.47 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): let `W` be a graphon on `(Ω₂, µ₂)` with `ρ_W > 0` and
`φ : Ω₁ → Ω₂` measure-preserving. Then `h(W^φ) = h(W)` (4.119), `k_{W^φ} = k_W ∘ φ` a.e. and
`ρ_{W^φ} = ρ_W` (4.120).

**Formalization Note.** `MeasurePreserving φ μ₁ μ₂` includes measurability of `φ`, as in the
paper's definition (App. A, p.81). -/
theorem lemma_4_26 {Ω₁ : Type*} {Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (μ₁ : Measure Ω₁) [IsProbabilityMeasure μ₁] (μ₂ : Measure Ω₂) [IsProbabilityMeasure μ₂]
    (W : Ω₂ → Ω₂ → ℝ) (hW : IsGraphon W) (hρ : 0 < density μ₂ W)
    (φ : Ω₁ → Ω₂) (hφ : MeasurePreserving φ μ₁ μ₂) :
    cheegerW μ₁ (pullback φ W) = cheegerW μ₂ W ∧
    degFun μ₁ (pullback φ W) =ᵐ[μ₁] (degFun μ₂ W ∘ φ) ∧
    density μ₁ (pullback φ W) = density μ₂ W := by sorry

end GraphonCheeger
