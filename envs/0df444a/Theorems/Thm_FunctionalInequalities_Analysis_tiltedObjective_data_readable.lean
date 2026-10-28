-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_tiltedObjective_data_readable
-- name    : FunctionalInequalities.Analysis.tiltedObjective_data_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:20.763042+00:00
-- url     : https://prove2.me/theorems/e3e2f5b2-8368-425f-a963-03a46f5caf8c
-- title:
--   Regularity and Coercive Decay of the Tilted Objective
-- statement:
--   This is a technical attainment lemma for a Legendre transform.
--
--   Let $E$ be a finite-dimensional real inner-product normed space, let $\phi:E\to\overline{\mathbb R}$ be a `ProperPotential`, and assume that $\phi$ is lower semicontinuous. If $y$ lies in the interior of $\{q:\phi^*(q)\ne+\infty\}$, define $G(z)=\langle z,y\rangle-\phi(z)$. Then:
--
--   1. $G$ is upper semicontinuous;
--   2. $G(z)\ne+\infty$ for every $z$;
--   3. $G(z)\ne-\infty$ for at least one $z$; and
--   4. there exist $a,b\in\mathbb R$ with $a>0$ such that, for every $z$,
--   $$G(z)\le b-a\|z\|.$$
--
--   The conclusion supplies the hypotheses for a separate upper-semicontinuous maximum theorem; it does not itself assert existence of a maximizer.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem tiltedObjective_data
--       (φ : E → EReal) (hφ : ProperPotential φ)
--       (hlsc : LowerSemicontinuous φ) (y : E)
--       (hy : y ∈ interior {q : E | legendre φ q ≠ ⊤}) :
--       let G : E → EReal := fun z => (inner ℝ z y : EReal) - φ z
--       UpperSemicontinuous G ∧
--         (∀ z, G z ≠ ⊤) ∧
--         (∃ z, G z ≠ ⊥) ∧
--         ∃ (a b : ℝ), 0 < a ∧ ∀ z,
--           G z ≤ ((b - a * ‖z‖ : ℝ) : EReal)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/LegendreVariation/Attainment`](https://prove2.me/theorems/8fff00c5-0262-4f99-9cab-27221baba48b).
--
--   Definition modules: [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Supporting theorems: [`exists_coercive_tilt_of_mem_interior_legendre_domain`](https://prove2.me/theorems/2a6ee0ab-9933-4999-9219-7fdf5606d335).
--
--   Previous: [`exists_coercive_tilt_of_mem_interior_legendre_domain`](https://prove2.me/theorems/2a6ee0ab-9933-4999-9219-7fdf5606d335) · Next: [`exists_legendre_maximizer_with_gradient_identity`](https://prove2.me/theorems/0a4c46db-2543-480e-9c88-e7e91f832b89).
--
--   [Source excerpt, lines 280–289](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/LegendreVariation/Attainment.lean#L280-L289) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/LegendreVariation/Attainment.lean#L277-L332 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.LegendreVariation.Attainment`, declaration `FunctionalInequalities.Analysis.tiltedObjective_data`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_LegendreVariation_Attainment

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.tiltedObjective_data_readable
    (φ : E → EReal) (hφ : ProperPotential φ)
    (hlsc : LowerSemicontinuous φ) (y : E)
    (hy : y ∈ interior {q : E | legendre φ q ≠ ⊤}) :
    let G : E → EReal := fun z => (inner ℝ z y : EReal) - φ z
    UpperSemicontinuous G ∧
      (∀ z, G z ≠ ⊤) ∧
      (∃ z, G z ≠ ⊥) ∧
      ∃ (a b : ℝ), 0 < a ∧ ∀ z,
        G z ≤ ((b - a * ‖z‖ : ℝ) : EReal) := by sorry
