-- Prove2me | Theorems.Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC
-- name    : ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/cc3e030d-3504-562f-97b4-8d549383feb0
-- title:
--   Gauss prolongation on the q-expansion modular function field
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure, let $A\subseteq L$ be a valuation subring, and let $\Gamma\le \mathrm{SL}(2,\mathbb{Z})$ be a subgroup containing the translation matrix $T=\begin{pmatrix}1&1\\0&1\end{pmatrix}$. For a field $K$, write $F(K)=\verb|qExpFunctionFieldC|\,K\,\Gamma$ for the intermediate field of $K((q))$ generated over $K$ by the ratios $\verb|intSeriesC|\,K\,p_f/\verb|intSeriesC|\,K\,p_g$, where $f,g$ are modular forms of one weight $k$ on the image of $\Gamma$ in $\mathrm{GL}(2,\mathbb{R})$, $p_f,p_g$ are integral power series with $\verb|IsIntegralQExp|$ for $f$ and $g$ respectively, and the denominator series over $K$ is nonzero; and let $F=\verb|laurentBaseChange|\,L\,F(\mathbb{Q})$ be the intermediate field of $L((q))$ generated over $L$ by the coefficientwise images of $F(\mathbb{Q})\subseteq \mathbb{Q}((q))$ under $\mathbb{Q}\to L$. The assertion is that there exists a regular prolongation $R$ of $A$ from $L$ to $F$ with residue target $F(k)$, $k=$ the residue field of $A$ — that is, a valuation subring $R.\verb|integers|$ of $F$ meeting $L$ exactly in $A$, together with a surjective ring homomorphism $R.\verb|residue|\colon R.\verb|integers|\to F(k)$ whose kernel is the maximal ideal, compatible with $A\to k$ on constants, and such that every nonzero element of $F$ becomes, after multiplication by a suitable constant in $L$, an element of $R.\verb|integers|$ with nonzero residue — satisfying in addition: (i) an element $f\in F$ lies in $R.\verb|integers|$ precisely when there are Laurent series $x,y$ with coefficients in $A$ such that the coefficientwise reduction of $y$ to $k((q))$ is nonzero and $f\cdot \iota(y)=\iota(x)$, where $\iota$ denotes coefficientwise inclusion $A((q))\to L((q))$; and (ii) for every $y\in A((q))$ whose image $\iota(y)$ lies in $F$, that image lies in $R.\verb|integers|$ and its residue, viewed inside $k((q))$, is the coefficientwise reduction of $y$.
--
--   This is the Gauss (or "inf") prolongation of a valuation of the constant field to a modular function field, read through $q$-expansions at $\infty$, in the setting of Deuring's theory of constant reductions; no hypothesis is imposed on the level or on the residue characteristic. It provides the valuation-theoretic carrier on which the later reduction arguments for modular curves with level structure operate, and is invoked by the statements describing the behaviour of level automorphisms under reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC
    (L : Type*) [Field L] [Algebra ℚ L] (A : ValuationSubring L)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hT : ModularGroup.T ∈ Γ) :
    ∃ R : AlgebraicCurve.RegularProlongation A
        (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))
        (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ),
      (∀ f : ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ),
        f ∈ R.integers ↔
          ∃ x y : LaurentSeries A, ModularCurve.coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
            (f : LaurentSeries L) * ModularCurve.coeffMap A.subtype y =
              ModularCurve.coeffMap A.subtype x) ∧
      ∀ (y : LaurentSeries A)
        (hy : ModularCurve.coeffMap A.subtype y ∈
          ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)),
        ∃ hO : (⟨ModularCurve.coeffMap A.subtype y, hy⟩ :
            ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)) ∈ R.integers,
          ((R.residue ⟨_, hO⟩ : ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ) :
              LaurentSeries (IsLocalRing.ResidueField A)) =
            ModularCurve.coeffMap (IsLocalRing.residue A) y := by sorry
