-- Prove2me | Theorems.Thm_GeoQAC_lemma_3_9
-- name    : GeoQAC.lemma_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:31:27.569398+00:00
-- url     : https://prove2.me/theorems/3cf1921d-9747-4eb2-b859-6c472fa5819c
-- title:
--   Lemma 3.9 — one layer increases $\Gamma$ by at most $O(w^3)$
-- statement:
--   Let $U=\prod_{g}R_g$ be a layer of product reflections with pairwise disjoint horizontal or vertical interval supports $G_g$ in a width-$w$ grid $[w]\times[h]$. Every pure state $|\psi\rangle$ satisfies
--   $$
--   \Gamma\big(U\psi U^\dagger\big)\le O(w^3)\cdot\Gamma(\psi).
--   $$
--   That is, there is an absolute constant $K_0$ with $\Gamma(U\psi U^\dagger)\le K_0\,w^3\,\Gamma(\psi)$ for every grid, every such layer and every pure state.
--
--   This is the key estimate of the lower bound: iterating it over the layers of a circuit bounds $\Gamma$ of its output.
--
--   Differences from the source:
--   - encoding: $O(w^3)$ → an absolute constant $K_0$, chosen before the grid, the layer and the state, with bound $K_0w^3$; reason: §2.1, p.9, asymptotic notation hides absolute constants.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Lemma 3.9, p.16 (restated p.20; constant at the end of the proof, p.23)

import Mathlib
import Definitions.Def_DHRUniq_IsUnitVec
import Definitions.Def_ObliviousRSP_pureState
import Definitions.Def_GeoQAC_IsInterval
import Definitions.Def_GeoQAC_lmv
import Definitions.Def_GeoQAC_ReflLayer

namespace GeoQAC

open DHRUniq (IsUnitVec)

open ObliviousRSP (pureState)

open Matrix

/-- **Lemma 3.9** (arXiv:2604.07178, version of 2026-11-03, p.16, restated p.20). Let
`U = ∏_{g∈G} R_g` be a layer of product reflections with pairwise disjoint horizontal or vertical
interval supports `G_g` in a width-`w` grid. Every pure state `|ψ⟩` satisfies
`Γ(UψU†) ≤ O(w³) · Γ(ψ)`.

**Formalization Note.** The `O(·)` constant `K₀` is absolute (§2.1, p.9: asymptotic notation hides
absolute constants): it is chosen before the grid, the layer and the state. The proof (p.23) gives
`K₀ w³ ≥ 2(w + 1) + 16w³`. `UψU†` is the pure state of `Uψ`; `ψ` is a unit vector. -/
theorem lemma_3_9 : ∃ K₀ : ℝ, ∀ (w h : ℕ) (L : ReflLayer (Pos w h)),
    (∀ S ∈ L.supp, IsInterval S) →
    ∀ ψ : (Pos w h → Bool) → ℂ, IsUnitVec ψ →
      lmv (pureState (L.matrix *ᵥ ψ)) ≤ K₀ * (w : ℝ) ^ 3 * lmv (pureState ψ) := by sorry

end GeoQAC
