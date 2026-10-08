-- Prove2me | Theorems.Thm_MonotoneCompStatics_Monotonicity_theorem4prime_selection
-- name    : MonotoneCompStatics.Monotonicity.theorem4prime_selection
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:31:25.591252+00:00
-- url     : https://prove2.me/theorems/64debe9a-8a18-4aae-bc3e-2d39d3cb0ff1
-- title:
--   Theorem 4′ (Monotone Selection Theorem)
-- statement:
--   Let $X$ be a lattice, $T$ a partially ordered set, $S:T\to 2^X$ a nondecreasing feasible-set correspondence under the strong set order, and $f:X\times T\to\mathbb R$. If $f(\cdot,t)$ is quasisupermodular on $X$ for every $t$ and $f$ has the strict single crossing property, then every selection from the maximizers is nondecreasing:
--
--   $$t\le t'\quad\Longrightarrow\quad x^*(t)\le x^*(t')\qquad\text{whenever }x^*(u)\in\operatorname{argmax}_{x\in S(u)}f(x,u)\text{ for }u=t,t'.$$
--
--   Strict single crossing is needed because an arbitrary choice among tied maximizers need not be monotone under weak single crossing.
--
--   **Formalization Note** A selection is represented by a function on an arbitrary domain $D\subseteq T$ where maximizers exist. No global existence of maximizers is assumed. The order on feasible sets includes empty sets; $f$ is curried in Lean.
-- source:
--   Milgrom and Shannon, Monotone Comparative Statics, Econometrica 62 (1994), p. 163 (PDF 8), Theorem 4′ (Monotone Selection Theorem)

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_MonotoneCompStatics_Monotonicity_argmaxOn
import Definitions.Def_MonotoneCompStatics_Monotonicity_QuasiSupermodularOn
import Definitions.Def_MonotoneCompStatics_Monotonicity_StrictSingleCrossing

namespace MonotoneCompStatics.Monotonicity

theorem theorem4prime_selection {X T : Type*} [Lattice X] [PartialOrder T]
    (f : X → T → ℝ) (S : T → Set X)
    (hS : ∀ ⦃t t' : T⦄, t ≤ t' → Supermodularity.Lattices.InducedSetOrder (S t) (S t'))
    (hq : ∀ t, QuasiSupermodularOn (fun x => f x t) Set.univ)
    (hsc : StrictSingleCrossing f) :
    ∀ (D : Set T) (xs : T → X), (∀ t ∈ D, xs t ∈ argmaxOn (fun x => f x t) (S t)) →
      MonotoneOn xs D := by sorry

end MonotoneCompStatics.Monotonicity
