-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_residue_jFun_sub_jQFun_sub
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.residue_jFun_sub_jQFun_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/a5d29f7b-fcb6-5415-a31a-ac103467e431
-- title:
--   Residues of j-a and j(q^q)-a on both prolongations
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of an algebraic closure of $\mathbb{Q}$, a positive integer $N$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$. Let `data` consist of a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair of $q$-expansions $(j, j_q)$, let `hKr` assert the Kronecker congruence that the reduction of $\Phi$ modulo $q$ equals $(X^q - Y)(X - Y^q)$, and let `hα`, `hβ` assert integrality of the two Hecke maps `heckeAlphaBar`, `heckeBetaBar` at level $N$ and prime $q$ over the algebraic closure of $\mathbb{Q}$. Let $P$ be a place specialisation of these data and $R$ a prolongation tuple over $P$, so that $R$ carries two regular prolongations $R_1, R_2$ of $A$ to `modularFunctionFieldBar (N * q)` (the base change to the algebraic closure of $\mathbb{Q}$ of the full modular function field of level $Nq$ inside Laurent series), each a valuation subring `integers` with a residue homomorphism onto `modularFunctionFieldFullC (ResidueField A) N`, together with the embedding $\iota$ of the latter into `modularFunctionFieldC k N`, the subfield of $\mathrm{LaurentSeries}\,k$ generated over $k$ by `jqModC k` and `jqNModC k N`. Assume $q \nmid N$ and let $a \in A$. Then, writing `jFun N q` for the element $j$ and `jQFun N q` for the $q$-fold expansion $j(\mathfrak q^q)$ of `modularFunctionFieldBar (N * q)`, both $j - a$ and $j(\mathfrak q^q) - a$ lie in $R_1$'s and in $R_2$'s ring of integers, and for these memberships the associated residues satisfy $\mathrm{res}_1(j - a) = \tilde\jmath - \mathrm{red}(a)$, $\mathrm{res}_2(j - a) = \tilde\jmath^{\,q} - \mathrm{red}(a)$, $\mathrm{res}_1(j(\mathfrak q^q) - a) = \tilde\jmath^{\,q} - \mathrm{red}(a)$ and $\mathrm{res}_2(j(\mathfrak q^q) - a) = \tilde\jmath - \mathrm{red}(a)$, where $\tilde\jmath$ denotes `jGeomGen k N`, the distinguished generator `jqModC k` of `modularFunctionFieldC k N`.
--
--   This is the Kronecker congruence $\Phi_q(X,Y) \equiv (X^q - Y)(X - Y^q) \pmod q$ read off on the two prolongations of $A$ to the function field of $X_0(Nq)$, corresponding to the two components of the special fibre at $q$: on one the $j$-line reduces to $\tilde\jmath$ and the $q$-isogenous $j$ to its $q$-th power, and on the other the roles are exchanged. It feeds the identification of the generic-point stalks of the Deligne–Rapoport model with rational function fields and the comparison of the two residue maps there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_residue_jFun_sub_jQFun_sub.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.residue_jFun_sub_jQFun_sub
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) (hqN : ¬ q ∣ N) (a : A) :
    ∃ (h₁ : ProlongationTuple.jFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers)
      (h₂ : ProlongationTuple.jFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₂.integers)
      (h₃ : ProlongationTuple.jQFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers)
      (h₄ : ProlongationTuple.jQFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₂.integers),
      R.residue₁ ⟨_, h₁⟩ = jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (red a) ∧
      R.residue₂ ⟨_, h₂⟩ = jGeomGen k N ^ q - algebraMap k ↥(modularFunctionFieldC k N) (red a) ∧
      R.residue₁ ⟨_, h₃⟩ = jGeomGen k N ^ q - algebraMap k ↥(modularFunctionFieldC k N) (red a) ∧
      R.residue₂ ⟨_, h₄⟩ = jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (red a) := by sorry
