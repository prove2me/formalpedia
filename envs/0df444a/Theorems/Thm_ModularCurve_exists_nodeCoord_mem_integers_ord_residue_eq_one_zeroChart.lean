-- Prove2me | Theorems.Thm_ModularCurve_exists_nodeCoord_mem_integers_ord_residue_eq_one_zeroChart
-- name    : ModularCurve.exists_nodeCoord_mem_integers_ord_residue_eq_one_zeroChart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/5d167a9b-0894-5532-9a41-9785232429ea
-- title:
--   Simple zero of jₚ - jᵖ on the zero-cusp chart
-- statement:
--   Let $p$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ whose residue field $k = \mathrm{ResidueField}(A)$ has characteristic $p$, and let $\bar F$ be a field equipped with a $k$-algebra structure. Let $C$ be a `ComponentChart` for $A$, the field `modularFunctionFieldBar p` (the intermediate field of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise images of the full modular function field of level $p$), and $\bar F$: thus a valuation subring `C.integers` of that field, a surjective ring homomorphism `C.residue` onto $\bar F$ with kernel the maximal ideal, a set of places `C.dom`, a finite set of nodes among the places of $\bar F$ over $k$, and a map `C.placeMap` satisfying the chart compatibilities. Let $X \in \bar F$ and let $c \mapsto \mathrm{xpl}(c)$ assign to each $c \in k$ a place of $\bar F$ over $k$, subject to the hypothesis that for all $c \in k$ and all $P \in k[T]$ the order $\mathrm{ord}_{\mathrm{xpl}(c)}(P(X))$ equals the multiplicity of $c$ as a root of $P$. Assume that the element $j$, given by the coefficientwise image under `coeffEmb` of the Laurent expansion `jq`, and the element $j_p$, the corresponding image of `qExpand ℚ p jq` (the expansion with exponents multiplied by $p$), both lie in `C.integers`, and that their residues satisfy $C.\mathrm{residue}(j_p) = X$ and $C.\mathrm{residue}(j) = X^p$. Let $a \in k$ satisfy $a^{p^2} = a$. Then $j_p - j^p$ lies in `C.integers` and the order of its residue at the place $\mathrm{xpl}(a^p)$ equals $1$.
--
--   On the chart of the component of $X_0(p)$ in characteristic $p$ through the cusp $0$, where $j_p$ reduces to the coordinate $X$ and $j$ to $X^p$ by Kronecker's congruence, the function $j_p - j^p$ reduces to $X - X^{p^2}$ and so cuts out each supersingular node transversally. The statement supplies the order-one condition used by [`ModularCurve.isAttached_ssAnnulus_zeroChart_of_chartSpec`](thm.html#ModularCurve.isAttached_ssAnnulus_zeroChart_of_chartSpec) when attaching a supersingular annulus with parameter $j_p - j^p$ to this chart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_nodeCoord_mem_integers_ord_residue_eq_one_zeroChart.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_ArithmeticGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_nodeCoord_mem_integers_ord_residue_eq_one_zeroChart
    (p : ℕ) [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [CharP (IsLocalRing.ResidueField ↥A) p]
    {Fbar : Type} [Field Fbar] [Algebra (IsLocalRing.ResidueField ↥A) Fbar]
    (C : ComponentChart A ↥(modularFunctionFieldBar p) Fbar)
    (X : Fbar) (xpl : IsLocalRing.ResidueField ↥A → Place (IsLocalRing.ResidueField ↥A) Fbar)
    (hord_poly : ∀ (c : IsLocalRing.ResidueField ↥A) (P : Polynomial (IsLocalRing.ResidueField ↥A)),
      (xpl c).ord (Polynomial.aeval X P) = (P.rootMultiplicity c : ℤ))
    (hjF : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full p (jq_mem p))⟩ : modularFunctionFieldBar p) ∈ C.integers)
    (hjpF : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (jqd_mem_full p (dvd_refl p))⟩ : modularFunctionFieldBar p) ∈ C.integers)
    (hres_jp : C.residue ⟨_, hjpF⟩ = X) (hres_j : C.residue ⟨_, hjF⟩ = X ^ p)
    (a : IsLocalRing.ResidueField ↥A) (ha2 : a ^ (p ^ 2) = a) :
    ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full p (dvd_refl p))⟩ : modularFunctionFieldBar p)
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full p (jq_mem p))⟩ : modularFunctionFieldBar p) ^ p
        ∈ C.integers,
      (xpl (a ^ p)).ord (C.residue ⟨_, h⟩) = 1 := by sorry
