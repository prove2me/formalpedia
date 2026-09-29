-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_residueSnd_zero_iff_residueFst_of_mem_jIntegralClosure
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.hasValue_residueSnd_zero_iff_residueFst_of_mem_jIntegralClosure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/bd837345-fbd0-538c-9c6a-31b3d1ad6b99
-- title:
--   Both branch residues vanish together at a supersingular node
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a nonzero level $N$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$; fix data $\mathrm{data}$ for the modular polynomial of level $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$) together with a proof $hKr$ that the reduction of $\Phi$ modulo $q$ equals $(X^q - Y)(X - Y^q)$, and proofs $h\alpha$, $h\beta$ that the two degeneracy maps $\mathrm{heckeAlphaBar}$, $\mathrm{heckeBetaBar}$ over $\overline{\mathbb{Q}}$ at level $N$ and prime $q$ are integral ring homomorphisms. Let $P$ be a place specialisation for these data and $R$ a prolongation tuple over $P$, with $k$ algebraically closed, and assume $q \nmid N$. Let $K$ be an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$, let $v$ be a place of $\mathrm{modularFunctionFieldC}\ k\ N$ over $k$ lying in $\mathrm{ssPlaces}\ q\ N\ k$, i.e. satisfying $\mathrm{IsSupersingularPlace}\ q\ N\ k$, and let $g$ be an element of $\mathrm{modularFunctionFieldBar}(Nq)$ whose underlying Laurent series lies in $\mathrm{NodeLocalized.jIntegralClosure}\ (Nq)\ A\ K$, that is, lies in $\mathrm{fieldOver}\ (Nq)\ K$ and is integral over the ring $\mathrm{jRing}\ A\ K$. Assume further that $g$ lies in the integers of both regular prolongations $R.R_1$ and $R.R_2$. Then the second-branch reduction $R.\mathrm{residue}_2(g)$, viewed in $\mathrm{modularFunctionFieldC}\ k\ N$, lies in the valuation subring of the translated place $\mathrm{arithFrobC}\ q\ k\ N \cdot v$ with residue $0$ there if and only if the first-branch reduction $R.\mathrm{residue}_1(g)$ lies in the valuation subring of $v$ with residue $0$ there. No finiteness of $K$ over $\mathbb{Q}$ is assumed.
--
--   This is the local form, at a supersingular point, of the gluing in the special fibre of $X_0(Nq)$ at $q$: the two copies of $X_0(N)$ are joined at the supersingular points, the second one along the arithmetic Frobenius, so a function integral over the $j$-ring takes a single value at the node, and in particular vanishes on one branch exactly when it vanishes on the other. It is used in the construction of functions with prescribed vanishing at the nodes, in [`ModularCurve.PlaceSpecialization.ProlongationTuple.exists_mem_jIntegralClosure_ord_residues_pos_and_eq_zero_of_ne`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.exists_mem_jIntegralClosure_ord_residues_pos_and_eq_zero_of_ne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_residueSnd_zero_iff_residueFst_of_mem_jIntegralClosure.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple
set_option synthInstance.maxHeartbeats 400000 in

theorem
ModularCurve.PlaceSpecialization.ProlongationTuple.hasValue_residueSnd_zero_iff_residueFst_of_mem_jIntegralClosure
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (v : Place k (modularFunctionFieldC k N)) (hv : v ∈ ssPlaces q N k)
    (g : ↥(modularFunctionFieldBar (N * q)))
    (hg : ((g : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.jIntegralClosure (N * q) A K))
    (h₁ : g ∈ R.R₁.integers) (h₂ : g ∈ R.R₂.integers) :
    (arithFrobC q k N • v).HasValue (R.residue₂ ⟨g, h₂⟩ : ↥(modularFunctionFieldC k N)) (0 : k) ↔
      v.HasValue (R.residue₁ ⟨g, h₁⟩ : ↥(modularFunctionFieldC k N)) (0 : k) := by sorry
