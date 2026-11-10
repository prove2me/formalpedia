-- Prove2me | Theorems.Thm_IntLInfty_Kan_linear_horn_filler_ambient
-- name    : IntLInfty.Kan.linear_horn_filler_ambient
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-10T03:11:07.348906+00:00
-- url     : https://prove2.me/theorems/20e70af2-852b-46f6-a690-d8abcb33e59c
-- title:
--   Linear (non-integral) horn fillers in the ambient spaces
-- statement:
--   For $S'\le S$ there are smooth families $Z$ of maps into $\mathrm{Amb}_r(S,m+1)$ with $\mathrm{res}\,Z(x,y)=y_2$, $d_iZ(x,y)=y_{1,i}$ for compatible horn data, $Z(x,\mathrm{kan}\,x)=x$, and a continuous linear section $s$ of $\mathrm{res}$: $$\mathrm{res}\circ s=\mathrm{id}.$$
--
--   Role: the linear filler (from Lemma 5.9) that the nonlinear fillers correct.
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

theorem linear_horn_filler_ambient (r : ℕ) (hr : 1 ≤ r) (L : ℕ → Type) [∀ i, AddCommGroup (L i)]
    [∀ i, Module ℝ (L i)] [∀ i, FiniteDimensional ℝ (L i)] (S S' : GenSys L)
    (h : ∀ i, S' i ≤ S i) :
    (∀ (m : ℕ) (j : Fin (m + 2)),
      ∃ Z : Amb r S (m + 1) → (({i : Fin (m + 2) // i ≠ j} → Amb r S m) × Amb r S' (m + 1)) →
          Amb r S (m + 1),
        (∀ x, ContDiff ℝ ∞ (Z x)) ∧
        (∀ x y, res h (Z x y) = y.2) ∧
        (∀ x (y : ({i : Fin (m + 2) // i ≠ j} → Amb r S m) × Amb r S' (m + 1)),
          HornCompat (fun q => faceAmb r S q) m j y.1 →
          (∀ i, faceAmb r S' m i.1 y.2 = res h (y.1 i)) → ∀ i, faceAmb r S m i.1 (Z x y) = y.1 i) ∧
        (∀ x, Z x (kanMap h m j x) = x)) ∧
    (∀ m, ∃ s : Amb r S' m →L[ℝ] Amb r S m, ∀ y, res h (s y) = y) := by sorry

end IntLInfty.Kan
