-- Prove2me | Theorems.Thm_ModelFreeBounds_Duality_lemma_EC_4_2
-- name    : ModelFreeBounds.Duality.lemma_EC_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:37.021921+00:00
-- url     : https://prove2.me/theorems/4270a5f8-786e-4a89-90c6-cd26f828d802
-- title:
--   Lemma EC.4.2, p. ec18 — under Assumption 2.1, Δ ∩ relint(Γ_ν) ≠ ∅ for every ν ∈ P(Ω); in particular Δ ∩ relint(Γ) ≠ ∅
-- statement:
--   Let $\Omega$ be a Polish space and consider a market with Borel payoffs $g_1,\dots,g_m$ and bid–ask prices $\underline\pi_j\le\overline\pi_j$ satisfying the no-arbitrage Assumption 2.1. Let $f:\Omega\to\mathbb R$ be Borel measurable and $\Delta=\prod_j[\underline\pi_j,\overline\pi_j]$. For a Borel probability measure $\nu$ on $\Omega$ let
--   $$\widetilde{\mathcal P}_\nu=\Big\{\mu\in\mathcal P(\Omega):\nu\ll\mu,\ \int_\Omega|f|+\sum_{j=1}^m|g_j|\,d\mu<\infty\Big\},\qquad \Gamma_\nu=\Big\{\int_\Omega g\,d\mu:\mu\in\widetilde{\mathcal P}_\nu\Big\}\subset\mathbb R^m,$$
--   and let $\Gamma$ be defined in the same way without the condition $\nu\ll\mu$. Then
--   $$\Delta\cap\operatorname{relint}(\Gamma_\nu)\neq\emptyset\quad\text{for every }\nu\in\mathcal P(\Omega),$$
--   and, in particular, $\Delta\cap\operatorname{relint}(\Gamma)\neq\emptyset$.
--
--   This is the constraint qualification under which the semi-infinite Fenchel duality applies in the proof of Theorem 2.4(iii); it also gives the forward direction of the fundamental theorem (Theorem 2.3).
--
--   **Formalization Note** $\operatorname{relint}$ is Mathlib's `intrinsicInterior ℝ` on `Fin m → ℝ` (it does not depend on the choice of norm). Integrability of $|f|+\sum_j|g_j|$ is written as integrability of $f$ and of every $g_j$. The "in particular" part is stated under the extra hypothesis that $\Omega$ is nonempty: for $\Omega=\emptyset$ there are no probability measures, $\Gamma=\emptyset$, and the first part is vacuous.
-- source:
--   Neufeld, Papapantoleon & Xiang, Model-free bounds for multi-asset options using option-implied information and their exact computation, arXiv:2006.14288v3, Lemma EC.4.2, p. ec18

import Mathlib
import Definitions.Def_ModelFreeBounds_Duality_Market

open MeasureTheory Filter Topology

namespace ModelFreeBounds.Duality

theorem lemma_EC_4_2 {Ω : Type*} [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    {m : ℕ} (M : Market Ω m) (hM : M.Standing) (hNA : M.NoArbitrage)
    (f : Ω → ℝ) (hf : Measurable f) :
    (∀ ν : Measure Ω, IsProbabilityMeasure ν →
      (M.box ∩ intrinsicInterior ℝ (M.momentSet f ν)).Nonempty) ∧
    (Nonempty Ω → (M.box ∩ intrinsicInterior ℝ (M.momentSetAll f)).Nonempty) := by sorry

end ModelFreeBounds.Duality
