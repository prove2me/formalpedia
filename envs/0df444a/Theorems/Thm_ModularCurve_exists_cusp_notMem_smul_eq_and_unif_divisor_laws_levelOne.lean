-- Prove2me | Theorems.Thm_ModularCurve_exists_cusp_notMem_smul_eq_and_unif_divisor_laws_levelOne
-- name    : ModularCurve.exists_cusp_notMem_smul_eq_and_unif_divisor_laws_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/b7c81ac8-424c-592a-a3f7-7cbffdd6db93
-- title:
--   Level-one cusp and uniformisers with divisors [w]-[∞̄]
-- statement:
--   Let $q$ be a prime and let $k$ be an algebraically closed field of characteristic $q$. Write $F =$ `modularFunctionFieldC k 1` for the intermediate field of the Laurent series field $k((t))$ generated over $k$ by the $q$-expansions `jqModC k` and `jqNModC k 1`, and consider its places in the sense of `Place`: valuation subrings of $F$ containing the image of $k$, proper in $F$, and principal ideal rings. Let $W$ be a finite set of such places whose members are exactly the elements of `ssPlaces q 1 k`, that is, those places that are rational, are affine geometric places, and whose value at `jGeomGen k 1` lies in `ssJSet q k`. Then there exist a place $\mathrm{cusp}$ of $F$ and two functions $\pi, \pi'$ from places of $F$ to elements of $F$ such that: $\mathrm{cusp} \notin W$; $\mathrm{cusp}$ is fixed by the action of the semilinear automorphism `arithFrobC q k 1`, given by applying $x \mapsto x^q$ to Laurent coefficients; and for every $w \in W$ and every place $v$ of $F$ one has $(\delta_w - \delta_{\mathrm{cusp}})(v) = \mathrm{ord}_v(\pi(w))$ and $(\delta_{\varphi w} - \delta_{\mathrm{cusp}})(v) = \mathrm{ord}_v(\pi'(w))$, where $\varphi =$ `arithFrobC q k 1`, the divisors are the indicated finitely supported $\mathbb{Z}$-valued functions on places, and $\mathrm{ord}_v$ is minus the logarithm of the adic valuation at $v$. The functions $\pi, \pi'$ are defined at all places, but the two divisor laws are asserted only for $w \in W$.
--
--   This provides the $j$-line ingredient of the level-one annulus datum: a Frobenius-fixed cusp avoiding the supersingular places, together with, for each supersingular place $w$, functions whose divisors are $[w] - [\mathrm{cusp}]$ and $[\varphi w] - [\mathrm{cusp}]$. It is used by [`ModularCurve.PlaceSpecialization.ProlongationTuple.exists_annulusDatumQ_laws_levelOne`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.exists_annulusDatumQ_laws_levelOne), the divisor laws being stated as identities of integer-valued functions on all places so as to match the form in which they are consumed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_cusp_notMem_smul_eq_and_unif_divisor_laws_levelOne.lean

import Mathlib
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_cusp_notMem_smul_eq_and_unif_divisor_laws_levelOne
    (q : ℕ) [Fact q.Prime] (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (W : Finset (Place k (modularFunctionFieldC k 1))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k) :
    ∃ (cusp : Place k (modularFunctionFieldC k 1)) (unifFst unifSnd : Place k (modularFunctionFieldC k 1) → ↥(modularFunctionFieldC k 1)),
      cusp ∉ W ∧ arithFrobC q k 1 • cusp = cusp ∧
      (∀ w ∈ W,
      (∀ v : Place k (modularFunctionFieldC k 1),
          ((Finsupp.single w (1 : ℤ) - Finsupp.single cusp 1 :
              Divisor k ↥(modularFunctionFieldC k 1)) v) = v.ord (unifFst w)) ∧
      (∀ v : Place k (modularFunctionFieldC k 1),
          ((Finsupp.single (arithFrobC q k 1 • w) (1 : ℤ) - Finsupp.single cusp 1 :
              Divisor k ↥(modularFunctionFieldC k 1)) v) = v.ord (unifSnd w))) := by sorry
