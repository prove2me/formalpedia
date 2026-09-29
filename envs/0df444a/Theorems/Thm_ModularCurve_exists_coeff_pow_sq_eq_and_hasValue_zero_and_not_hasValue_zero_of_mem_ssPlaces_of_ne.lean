-- Prove2me | Theorems.Thm_ModularCurve_exists_coeff_pow_sq_eq_and_hasValue_zero_and_not_hasValue_zero_of_mem_ssPlaces_of_ne
-- name    : ModularCurve.exists_coeff_pow_sq_eq_and_hasValue_zero_and_not_hasValue_zero_of_mem_ssPlaces_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/436e4494-701b-54cb-bc19-27612367bf71
-- title:
--   Separating a supersingular place by an 𝔽_{q²}-rational affine function
-- statement:
--   Let $q$ be a prime, $N$ a nonzero natural number with $q \nmid N$, and $k$ an algebraically closed field of characteristic $q$. Work inside the field $F =$ `modularFunctionFieldC k N`, the intermediate field of the Laurent series field $k((\mathsf{q}))$ generated over $k$ by the two series `jqModC k` and `jqNModC k N` (the latter being the $N$-fold $\mathsf{q}$-expansion rescaling of the former). Places of $F$ over $k$ are valuation subrings of $F$ that contain the image of $k$, are proper, and are principal ideal rings. Let $w, w'$ be two such places with $w \neq w'$, and assume $w$ lies in `ssPlaces q N k`, i.e. $w$ is rational, both `jGeomGen k N` and `jNGeomGen k N` lie in the valuation subring of $w$ (so $w$ is an affine geometric place), and the value of `jGeomGen k N` at $w$ lies in `ssJSet q k`. Then there exists $t \in F$ such that: every Laurent coefficient $c_n$ of $t$ satisfies $c_n^{q^2} = c_n$; $t$ lies in the valuation subring of every place $u$ of $F$ at which `jGeomGen k N` and `jNGeomGen k N` are both regular; $t$ lies in the valuation subring of $w$ with residue the image of $0$; and the corresponding statement fails at $w'$, i.e. it is not the case that $t$ lies in the valuation subring of $w'$ with residue the image of $0$.
--
--   This is the separation statement used to isolate a single supersingular point of the characteristic-$q$ fibre of the modular curve of level $N$ from any other place, by an affine function whose $\mathsf{q}$-expansion has coefficients in $\mathbb{F}_{q^2}$, reflecting the rationality of supersingular points over the field with $q^2$ elements. It is invoked in the construction of prolongation tuples at place specialisations, where local uniformisers and residue orders at the nodes of the special fibre are produced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_coeff_pow_sq_eq_and_hasValue_zero_and_not_hasValue_zero_of_mem_ssPlaces_of_ne.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

theorem
ModularCurve.exists_coeff_pow_sq_eq_and_hasValue_zero_and_not_hasValue_zero_of_mem_ssPlaces_of_ne
    {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (hqN : ¬ q ∣ N) (w w' : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k) (hne : w ≠ w') :
    ∃ t : ↥(modularFunctionFieldC k N),
      (∀ n : ℤ, ((t : LaurentSeries k).coeff n) ^ (q ^ 2) = (t : LaurentSeries k).coeff n) ∧
      (∀ u : Place k (modularFunctionFieldC k N), IsAffineGeomPlace k N u → t ∈ u.toValuationSubring) ∧
      w.HasValue t (0 : k) ∧ ¬ w'.HasValue t (0 : k) := by sorry
