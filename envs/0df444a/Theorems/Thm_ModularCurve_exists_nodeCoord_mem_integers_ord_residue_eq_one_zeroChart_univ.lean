-- Prove2me | Theorems.Thm_ModularCurve_exists_nodeCoord_mem_integers_ord_residue_eq_one_zeroChart_univ
-- name    : ModularCurve.exists_nodeCoord_mem_integers_ord_residue_eq_one_zeroChart_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/f0785c09-2dc0-5484-b9da-108b61ba5714
-- title:
--   Node coordinate jₚ-jᵖ has a simple zero
-- statement:
--   Let $p$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ whose residue field $k = \mathrm{ResidueField}(A)$ has characteristic $p$, and let $\bar F$ be a field extension of $k$. Let $C$ be a component chart of the field $\mathrm{modularFunctionFieldBar}\,p$ — the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise images of the full level-$p$ modular function field — over $A$ with residue field $\bar F$: that is, a valuation subring $C.\mathrm{integers}$ of that field, a surjective ring homomorphism $C.\mathrm{residue}$ onto $\bar F$ whose kernel is the maximal ideal, a set of places, a finite set of nodes and a map on places, subject to the compatibility axioms of `ComponentChart` (only the first two pieces enter here). Let $X \in \bar F$ and let $c \mapsto \mathrm{xpl}(c)$ assign to each $c \in k$ a place of $\bar F$ over $k$, such that for every $c$ and every $P \in k[T]$ one has $\mathrm{ord}_{\mathrm{xpl}(c)}(P(X)) = \mathrm{mult}_c(P)$. Assume the elements $j$ and $j_p$ of the field, obtained by coefficientwise base change from the $q$-expansion `jq` and from its image under $q \mapsto q^{p}$, both lie in $C.\mathrm{integers}$, with $C.\mathrm{residue}(j_p) = X$ and $C.\mathrm{residue}(j) = X^{p}$. Then for every $a \in k$ with $a^{p^{2}} = a$ the element $j_p - j^{p}$ lies in $C.\mathrm{integers}$ and the order of its residue at the place $\mathrm{xpl}(a^{p})$ equals $1$.
--
--   On the chart of the mod-$p$ reduction of $X_0(p)$ along the component through the cusp $0$, where $j_p$ reduces to the coordinate $X$ and $j$ to $X^{p}$ by Kronecker's congruence, this says that the node coordinate $G = j_p - j^{p}$ is chart-integral and cuts out each supersingular node $X = a^{p}$ (with $a^{p^2}=a$) transversally. It is the order-one half of the attachment of the supersingular annulus with parameter $G$ to this chart, used by [`ModularCurve.isAttached_ssAnnulus_zeroChart_of_chartSpec_univ`](thm.html#ModularCurve.isAttached_ssAnnulus_zeroChart_of_chartSpec_univ).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_nodeCoord_mem_integers_ord_residue_eq_one_zeroChart_univ.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_ArithmeticGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_nodeCoord_mem_integers_ord_residue_eq_one_zeroChart_univ
    (p : ℕ) [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [CharP (IsLocalRing.ResidueField ↥A) p]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField ↥A) Fbar]
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
