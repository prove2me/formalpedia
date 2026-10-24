-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_eventually_affineMaximum_sub_le_legendre_408915f
-- name    : FunctionalInequalities.Analysis.eventually_affineMaximum_sub_le_legendre_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:16:34.965233+00:00
-- url     : https://prove2.me/theorems/741e5cf7-9eb1-4742-b4fb-f8cdf65902bd
-- title:
--   Eventual Affine-Maximum Lower Bound for Legendre Transforms
-- statement:
--   This formalizes equation (60) of Cordero-Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1).
--
--   Let $E$ be a real inner-product normed space, let $\phi_j:E\to\overline{\mathbb R}$ be a sequence of extended-real functions, and let $\psi:E\to\overline{\mathbb R}$. Let $s\subset E$ be a nonempty finite set. Assume every $\psi(x)$ for $x\in s$ is neither $+\infty$ nor $-\infty$, and that $\phi_j(x)\to\psi(x)$ at each $x\in s$. For $\varepsilon>0$, eventually in $j$ and for every $y\in E$,
--   $$\bigl(\operatorname{affineMaximum}(s,\psi_{|s}^{\mathrm{toReal}},y)-\varepsilon\bigr)
--   \le (\phi_j)^*(y),$$
--   where the left side is embedded into `EReal` and $(\phi_j)^*$ is `legendre (φ j)`.
--
--   The statement provides a bound uniform in the dual point $y$, obtained from pointwise convergence at finitely many vertices. It is a geometric approximation tool for Legendre transforms.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/AffineMaximum.lean#L100-L131 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.AffineMaximum`, declaration `FunctionalInequalities.Analysis.eventually_affineMaximum_sub_le_legendre`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open Filter Set
open scoped Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.eventually_affineMaximum_sub_le_legendre_408915f
    (φ : ℕ → E → EReal) (ψ : E → EReal) (s : Finset E) (hs : s.Nonempty)
    (hfin : ∀ x ∈ s, ψ x ≠ ⊤ ∧ ψ x ≠ ⊥)
    (hlim : ∀ x ∈ s, Tendsto (fun j => φ j x) atTop (𝓝 (ψ x)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ y : E,
      ((affineMaximum s hs (fun x => (ψ x).toReal) y - ε : ℝ) : EReal) ≤
        legendre (φ j) y := by sorry
