-- Prove2me | Theorems.Thm_ModularCurve_exists_equiv_ssJSet_coe_eq_evalAt_jGeomGen_of_forall_mem_iff_mem_ssPlaces
-- name    : ModularCurve.exists_equiv_ssJSet_coe_eq_evalAt_jGeomGen_of_forall_mem_iff_mem_ssPlaces
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/428f1875-ac9d-5a55-a736-8cd8ce3b8025
-- title:
--   Supersingular places biject with supersingular j-invariants via evaluation
-- statement:
--   Fix a natural number $p$ and a field $k$ with decidable equality, and work with the level-one modular function field $\mathtt{modularFunctionFieldC }k\ 1$, the intermediate field of the Laurent series field $k((q))$ generated over $k$ by the two series $\mathtt{jqModC }k$ and $\mathtt{jqNModC }k\ 1$. Let $W$ be a finite set of places of this field over $k$ (a place being a valuation subring containing $k$, distinct from the whole field, and a principal ideal ring), and assume that a place $w$ belongs to $W$ if and only if it belongs to $\mathtt{ssPlaces }p\ 1\ k$, i.e. $w$ satisfies `IsRational`, satisfies `IsAffineGeomPlace`, and the value $w.\mathtt{evalAt}(\mathtt{jGeomGen }k\ 1)$ obtained by reducing the moduli generator $\mathtt{jqModC }k$ into the residue field and pulling it back to $k$ lies in $\mathtt{ssJSet }p\ k$, the set of those $j \in k$ such that every elliptic Weierstrass curve over $k$ with $j$-invariant $j$ has no nonzero $k$-point killed by $p$. The conclusion is that there exists a bijection $\tau$ from $W$ onto $\mathtt{ssJSet }p\ k$ with $\tau(w) = w.\mathtt{evalAt}(\mathtt{jGeomGen }k\ 1)$ for all $w \in W$.
--
--   This is the dictionary between the supersingular points of the level-one modular curve over $k$ and the supersingular $j$-invariants in $k$, realised by evaluating the moduli generator at a place; it packages the classical identification of affine places of the $j$-line with points of the affine line. It supplies the indexing bijection used in the Deligne–Rapoport model packages, where the supersingular points of the special fibre are enumerated together with their widths.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_equiv_ssJSet_coe_eq_evalAt_jGeomGen_of_forall_mem_iff_mem_ssPlaces.lean

import Mathlib
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_SpecializeModuli
import Theorems.Thm_ModularCurve_mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_equiv_ssJSet_coe_eq_evalAt_jGeomGen_of_forall_mem_iff_mem_ssPlaces
    (p : ℕ) (k : Type*) [Field k] [DecidableEq k]
    (W : Finset (Place k (modularFunctionFieldC k 1)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces p 1 k) :
    ∃ τ : ↥W ≃ ↥(ssJSet p k),
      ∀ w : ↥W, ((τ w : k)) = (w : Place k (modularFunctionFieldC k 1)).evalAt (jGeomGen k 1) := by sorry
