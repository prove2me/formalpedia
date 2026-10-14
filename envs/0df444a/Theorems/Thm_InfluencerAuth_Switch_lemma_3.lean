-- Prove2me | Theorems.Thm_InfluencerAuth_Switch_lemma_3
-- name    : InfluencerAuth.Switch.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:12:35.714091+00:00
-- url     : https://prove2.me/theorems/f4a7707e-4477-4353-a7f6-59b258ce4b6a
-- title:
--   Lemma 3, p. 6 — value of always being inauthentic: V̲(A) = ∫₀^∞ e^{−rs}γφ/[1 + ((1−A)/A)e^{−γβs}] ds
-- statement:
--   Let $0<\gamma<1$, $\varphi>1$ with $\gamma\varphi>1$, $\beta>0$, $r>0$ and $A_0\in(0,1)$. Under the policy of always being inauthentic, awareness grows according to $\frac{dA_u}{du}=\gamma\beta A_u(1-A_u)$. Then:
--
--   1. the always-inauthentic policy has an admissible awareness path from $A_0$, and
--   2. every such path $A$ earns the discounted profit
--   $$
--   \int_0^\infty e^{-ru}\,\gamma\varphi\,A_u\,du=\underline V(A_0)=\int_0^\infty \frac{e^{-rs}\,\gamma\varphi}{1+\frac{1-A_0}{A_0}\,e^{-\gamma\beta s}}\,ds .
--   $$
--
--   This closed form is the value the influencer compares against when she considers deviating from permanent inauthenticity, and its derivative (3) drives the switching rule of Proposition 1.
--
--   **Formalization Note** The paper states the lemma at a general time $t$ with $s=u-t$; by time invariance it is stated at $t=0$. The existence clause rules out a vacuous reading.
-- source:
--   Nistor, Selove, Villas-Boas, Management Science (Articles in Advance 2024), Lemma 3, p. 6

import Mathlib
import Definitions.Def_InfluencerAuth_Switch_Model
import Definitions.Def_InfluencerAuth_Switch_ClosedForms

open MeasureTheory Set Filter Topology

namespace InfluencerAuth.Switch

/-- Lemma 3 (p. 6): value of always being inauthentic. -/
theorem lemma_3 (γ φ β r : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hφ : 1 < φ)
    (hβ : 0 < β) (hr : 0 < r) (hγφ : 1 < γ * φ) (A₀ : ℝ) (hA₀ : A₀ ∈ Set.Ioo (0 : ℝ) 1) :
    (∃ A : ℝ → ℝ, IsPath β γ A₀ Set.univ A) ∧
    ∀ A : ℝ → ℝ, IsPath β γ A₀ Set.univ A →
      discountedProfit γ φ r Set.univ A = inauthValue γ φ β r A₀ := by sorry

end InfluencerAuth.Switch
