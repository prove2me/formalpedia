-- Prove2me | Theorems.Thm_ModularCurve_exists_ssAnnulus_centred_of_widthOne_level
-- name    : ModularCurve.exists_ssAnnulus_centred_of_widthOne_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/e04ebd74-9aef-573f-b0fb-8182bba7061f
-- title:
--   Width-one supersingular annulus on X₀(q), at level q
-- statement:
--   Let $q\ge 5$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$, let $k$ be an algebraically closed field of characteristic $q$, and let $\mathrm{red}\colon A\to k$ be a ring homomorphism whose zero set is exactly the maximal ideal of $A$ (i.e. $\mathrm{red}\,c=0\iff c\in\mathfrak{m}_A$). Let $a\in k$ lie in `ssJSet q k`, the set of elements $j$ such that every elliptic Weierstrass curve over $k$ with $j$-invariant $j$ has trivial $q$-torsion, and assume $a^{q^2}=a$, $a\ne 0$ and $a\ne 1728$. Write $F=$ `modularFunctionFieldBar q`, the subfield of $\overline{\mathbb{Q}}((\mathsf{q}))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of `modularFunctionFieldFull q`, and let $j\in F$ be the class of the Laurent series `jq` and $j_q\in F$ that of `qExpand ℚ q jq` (the series obtained by multiplying all exponents by $q$). The assertion is the existence of two annuli $\mathrm{An},\mathrm{An}'$ over $A$ in $F$ — each consisting of a set of places of $F$ over $\overline{\mathbb{Q}}$, a parameter in $F$ and a modulus in $\mathfrak{m}_A$, subject to the axioms of `Annulus` (rationality and unit properties of the places in the domain, a bijection between the domain and the admissible centres in $\mathfrak{m}_A$, $\operatorname{ord}_P(\mathrm{param}-\mathrm{param}(P))=1$, and the unit principle) — such that: $\mathrm{An}'.\mathrm{dom}=\mathrm{An}.\mathrm{dom}$, $\mathrm{An}'.\mathrm{modulus}=\mathrm{An}.\mathrm{modulus}$, this common modulus is nonzero in $\overline{\mathbb{Q}}$, and $\mathrm{An}'.\mathrm{param}\cdot\mathrm{An}.\mathrm{param}$ equals the image of the modulus in $F$; a place $W$ lies in $\mathrm{An}.\mathrm{dom}$ if and only if there are $x,y\in A$ with $\mathrm{red}\,x=a$, $\operatorname{ord}_W(j-x)>0$ and $\mathrm{red}\,y=a^{q}$, $\operatorname{ord}_W(j_q-y)>0$; $\mathrm{An}.\mathrm{param}=j_q-j^{\,q}$; and $\mathrm{An}.\mathrm{modulus}$ is the image of the natural number $q$ in $A$.
--
--   This is the local description, in the style of Deligne–Rapoport, of the semistable model of $X_0(q)$ near a supersingular point with $j$-invariant $a$ defined over $\mathbb{F}_{q^2}$ and distinct from $0$ and $1728$: the two branches $j\equiv a$ and $j_q\equiv a^{q}$ cross in a single node, realised as a pair of annuli of width one with parameters multiplying to $q$ and with $j_q-j^{\,q}$ as parameter. It is the form of the statement used by the construction of component charts and attached annuli for prolongation tuples of place specialisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_ssAnnulus_centred_of_widthOne_level.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.exists_ssAnnulus_centred_of_widthOne_level
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hq : 5 ≤ q) (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728) :
    ∃ (An An' : Annulus A ↥(modularFunctionFieldBar q)),
      (An'.dom = An.dom ∧ An'.modulus = An.modulus ∧
        ((An.modulus : AlgebraicClosure ℚ) ≠ 0) ∧
        An'.param * An.param
          = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar q)
              ((An.modulus : AlgebraicClosure ℚ))) ∧
      (∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar q),
        W ∈ An.dom ↔
          ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full q (jq_mem q))⟩ : modularFunctionFieldBar q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar q) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full q (dvd_refl q))⟩ : modularFunctionFieldBar q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar q) (y : AlgebraicClosure ℚ))))) ∧
      An.param = (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full q (dvd_refl q))⟩ : modularFunctionFieldBar q)
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full q (jq_mem q))⟩ : modularFunctionFieldBar q) ^ q ∧
      An.modulus = ((q : ℕ) : A) := by sorry
