-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residue_jFun_jqFun
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue_jFun_jqFun
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/1b4ddba0-f27d-55de-be96-d51a328583d2
-- title:
--   Residues of j and j_q on a level-one prolongation pair
-- statement:
--   Fix a prime $q$ and a valuation subring $A$ of $\overline{\mathbb Q}$ lying over $q$, in the sense that $q$ belongs to the nonunits of $A$; let $k$ be a field of characteristic $q$ and $red : A \to k$ a ring homomorphism. Let `data` be modular polynomial data for $q$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$), let `hKr` assert Kronecker's congruence $\Phi \equiv (X^q - Y)(X - Y^q)$ modulo $q$, and let `hα`, `hβ` assert integrality of the two Hecke homomorphisms $\overline{\alpha}$, $\overline{\beta}$ at level $1$ and prime $q$. Given a place specialisation $P$ of these data and a level-one prolongation pair $V$ for $P$ — consisting of a lift $\overline{red}$ of $red$ to the residue field of $A$, a coefficientwise embedding $\iota$, and two regular prolongations $V.R_1$, $V.R_2$ of $A$ from $\overline{\mathbb Q}$ to $\overline{\mathbb Q}\cdot F_{1\cdot q}$ with residue field $\mathrm{modularFunctionFieldFullC}$ over the residue field of $A$, the first computing residues by coefficientwise reduction and the second obtained from the first by the Fricke involution — the conclusion asserts that `jFun` (the $q$-expansion of $j$) and `jqFun` (that of $j(q\tau)$) lie in the integers of both prolongations, and that, as Laurent series over the residue field of $A$, $\mathrm{res}_1(j) = \bar j$, $\mathrm{res}_1(j_q) = \bar j^{\,q}$, $\mathrm{res}_2(j_q) = \bar j$ and $\mathrm{res}_2(j) = \bar j^{\,q}$, where $\bar j$ denotes `jqModC`, the series $t^{-1}$ times the reduction of the numerator of the $j$-expansion.
--
--   This is Kronecker's congruence read on the two components of $X_0(q)$ in characteristic $q$: on the component carrying the first prolongation one has $j_q = j^{\,q}$, on its Fricke transport $j = j_q^{\,q}$. It is used in the construction of the level-one specialisation charts and in the determination of the branch divisor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residue_jFun_jqFun.lean

import Definitions.Def_ModularCurve_LevelOneProlongationPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve IsLocalRing ModularCurve
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue_jFun_jqFun
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime q)
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (V : P.LevelOneProlongationPair) :
    ∃ (h₁ : PlaceSpecialization.jFun (q := q) ∈ V.R₁.integers)
      (h₂ : PlaceSpecialization.jqFun (q := q) ∈ V.R₁.integers)
      (h₃ : PlaceSpecialization.jqFun (q := q) ∈ V.R₂.integers)
      (h₄ : PlaceSpecialization.jFun (q := q) ∈ V.R₂.integers),
      ((V.R₁.residue ⟨_, h₁⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
          = jqModC (ResidueField A) ∧
      ((V.R₁.residue ⟨_, h₂⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
          = jqModC (ResidueField A) ^ q ∧
      ((V.R₂.residue ⟨_, h₃⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
          = jqModC (ResidueField A) ∧
      ((V.R₂.residue ⟨_, h₄⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
          = jqModC (ResidueField A) ^ q := by sorry
