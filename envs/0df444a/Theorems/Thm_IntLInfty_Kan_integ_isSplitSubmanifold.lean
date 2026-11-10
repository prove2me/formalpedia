-- Prove2me | Theorems.Thm_IntLInfty_Kan_integ_isSplitSubmanifold
-- name    : IntLInfty.Kan.integ_isSplitSubmanifold
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-10T02:11:11.307485+00:00
-- url     : https://prove2.me/theorems/717fedf0-52ab-4780-8912-d4761eff74ec
-- title:
--   $(\int_S)_m$ is a split submanifold
-- statement:
--   For an $L_\infty$-structure $\delta$ and a generator system $S$ closed under $\delta$, every level of $\int_S$ is a $C^\infty$ split submanifold of its ambient Banach space: $$\delta(S)\subseteq A_S\implies (\int_S)_m\subseteq \mathrm{Amb}_r(S,m)\ \text{split}.$$
--
--   Role: step K0b of the proof: the split-submanifold conditions of every Kan fibration in Theorem 5.10.
-- source:
--   Henriques, Integrating L-infinity algebras, Compositio Math. 144 (2008), arXiv:math/0603563v2, https://arxiv.org/abs/math/0603563, proof of Theorem 5.10 (Section 5, pp. 15-17)

import Mathlib
import Definitions.Def_IntLInfty_Kan_CE
import Definitions.Def_IntLInfty_Kan_Forms
import Definitions.Def_IntLInfty_Kan_Manifold
import Definitions.Def_IntLInfty_Kan_Integ

set_option autoImplicit false

open scoped ContDiff

namespace IntLInfty.Kan

theorem integ_isSplitSubmanifold (r : ℕ) (hr : 1 ≤ r) (L : ℕ → Type) [∀ i, AddCommGroup (L i)]
    [∀ i, Module ℝ (L i)] [∀ i, FiniteDimensional ℝ (L i)] (δ : LInfty L) (S : GenSys L)
    (hcl : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → δ.δ (gen L i ξ) ∈ genAlg L S) (m : ℕ) :
    IsSplitSubmanifold (integ r δ S m) := by sorry

end IntLInfty.Kan
