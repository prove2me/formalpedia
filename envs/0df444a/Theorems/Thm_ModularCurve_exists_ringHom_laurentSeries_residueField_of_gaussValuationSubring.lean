-- Prove2me | Theorems.Thm_ModularCurve_exists_ringHom_laurentSeries_residueField_of_gaussValuationSubring
-- name    : ModularCurve.exists_ringHom_laurentSeries_residueField_of_gaussValuationSubring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/56140f76-6a7a-5d4e-8e35-548e29d6e2af
-- title:
--   Gauss valuation ring: coefficientwise reduction to κ((q))
-- statement:
--   Let $L$ be a field, $A\subseteq L$ a valuation subring with residue field $\kappa=\mathrm{IsLocalRing.ResidueField}\ A$, let $F$ be an intermediate field of the extension $L\subseteq L(\!(q)\!)$ of the field of formal Laurent series, and let $W$ be a valuation subring of $F$. Write `coeffMap` for the ring homomorphism on Laurent series induced coefficientwise by a ring homomorphism of coefficients, applied here along the inclusion $A\hookrightarrow L$ and along the residue map $A\to\kappa$. Assume that $W$ is characterised by Gauss presentations: for every $f\in F$, one has $f\in W$ if and only if there are $x,y\in A(\!(q)\!)$ whose coefficientwise reduction satisfies $\bar y\neq 0$ in $\kappa(\!(q)\!)$ and such that, in $L(\!(q)\!)$, $f\cdot y=x$ after pushing $x,y$ forward along $A\hookrightarrow L$. The conclusion is that there exists a ring homomorphism $\mathrm{red}\colon W\to\kappa(\!(q)\!)$ with two properties: first, $\mathrm{red}(f)=0$ holds exactly when $f$, viewed in $F$, lies in `W.nonunits`; and second, for every $f\in W$ and every pair $x,y\in A(\!(q)\!)$ with $\bar y\neq 0$ and $f\cdot y=x$ in $L(\!(q)\!)$, one has $\mathrm{red}(f)\cdot\bar y=\bar x$ in $\kappa(\!(q)\!)$.
--
--   This is the $q$-expansion (Gauss lemma) reduction map for the Gauss valuation ring attached to a valuation subring $A$ of the constant field $L$: coefficientwise reduction of $q$-expansions is well defined on $W$, is multiplicative and additive, and has the maximal ideal of $W$ as its kernel, so that the residue field of $W$ embeds into $\kappa(\!(q)\!)$. It is used in the analysis of Igusa nodes on modular curves of full level, where reductions of $q$-expansions at a place above the relevant prime are compared.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_ringHom_laurentSeries_residueField_of_gaussValuationSubring.lean

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.exists_ringHom_laurentSeries_residueField_of_gaussValuationSubring
    {L : Type*} [Field L] (A : ValuationSubring L) (F : IntermediateField L (LaurentSeries L))
    (W : ValuationSubring ↥F)
    (hW : ∀ f : ↥F, f ∈ W ↔ ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
      (f : LaurentSeries L) * coeffMap A.subtype y = coeffMap A.subtype x) :
    ∃ red : ↥W →+* LaurentSeries (IsLocalRing.ResidueField ↥A),
      (∀ f : ↥W, red f = 0 ↔ (f : ↥F) ∈ W.nonunits) ∧
      ∀ (f : ↥W) (x y : LaurentSeries ↥A), coeffMap (IsLocalRing.residue ↥A) y ≠ 0 →
        ((f : ↥F) : LaurentSeries L) * coeffMap A.subtype y = coeffMap A.subtype x →
        red f * coeffMap (IsLocalRing.residue ↥A) y = coeffMap (IsLocalRing.residue ↥A) x := by sorry
