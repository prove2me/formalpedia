-- Prove2me | Theorems.Thm_ModularCurve_NodeLocalized_exists_ringEquiv_modularLocalizedAtPoint_coe_eq_frickeInvolutionBar
-- name    : ModularCurve.NodeLocalized.exists_ringEquiv_modularLocalizedAtPoint_coe_eq_frickeInvolutionBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/b8d6ca15-d46e-59d6-8368-52c2b0afc488
-- title:
--   Fricke involution exchanges node rings at (a,a^q) and (a^q,a)
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red}\colon A \to k$, an element $a \in k$ with $a^{q^2} = a$, and an intermediate field $K$ of $\overline{\mathbb Q}/\mathbb Q$. Write $A_0 = \mathrm{coeffSubring}\,A\,K$ for the subring $A \cap K$ of $\overline{\mathbb Q}$ and $\mathrm{red}_0 = \mathrm{redRestrict}\,\mathrm{red}\,K$ for the restriction of $\mathrm{red}$ to it. For $b, c \in k$ let $R(b,c) = \mathrm{modularLocalizedAtPoint}\,(1\cdot q)\,A_0\,\mathrm{red}_0\,b\,c$ be the subring of $\overline{\mathbb Q}(\!(\mathsf q)\!)$ consisting of those Laurent series $f$ for which there are $r, s \in A_0[X_0,X_1]$ with $s(b,c) \neq 0$ after applying $\mathrm{red}_0$ to the coefficients and $f \cdot s(j, j_q) = r(j, j_q)$, where $j, j_q$ denote the two $q$-expansions $\mathrm{jqModC}$ and $\mathrm{jqNModC}$ at level $1\cdot q$ and coefficients enter as constant series. The assertion is that there exists a ring isomorphism $\sigma \colon R(a, a^q) \xrightarrow{\sim} R(a^q, (a^q)^q)$ such that: (i) for every $g \in R(a,a^q)$ whose underlying Laurent series lies in $\mathrm{modularFunctionFieldBar}\,(1\cdot q)$, the field obtained from $\mathrm{modularFunctionFieldFull}\,(1\cdot q)$ by base change to $\overline{\mathbb Q}$ inside $\overline{\mathbb Q}(\!(\mathsf q)\!)$, the Laurent series underlying $\sigma(g)$ equals that of $\mathrm{frickeInvolutionBar}\,(1\cdot q)$ applied to $g$; and (ii) $\sigma$ intertwines the two evaluation maps $\mathrm{modularEvalAt}$ from $A_0[X_0,X_1]$ with the renaming that swaps the two variables, i.e. $\sigma(p(j,j_q)) = p(j_q,j)$ computed in $R(a^q,(a^q)^q)$.
--
--   This records the action of the Fricke (Atkin–Lehner) involution $w_q$ on the local rings of the plane model of $X_0(q)$ at the supersingular-type points $(a,a^q)$ of the special fibre: $w_q$ exchanges $j$ and $j_q$, hence carries the ring localised at $(a,a^q)$ isomorphically onto the one localised at $(a^q,a)$. It is the device by which statements proved for the branch through the cusp $\infty$ are transported to the second branch at a node, and it is cited in the construction of crossing presentations and two-branch normalisations in the node-descent analysis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_NodeLocalized_exists_ringEquiv_modularLocalizedAtPoint_coe_eq_frickeInvolutionBar.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_NodeLocalizedPresentation
import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve ModularCurve.NodeLocalized

theorem ModularCurve.NodeLocalized.exists_ringEquiv_modularLocalizedAtPoint_coe_eq_frickeInvolutionBar
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) (a : k) (ha2 : a ^ (q ^ 2) = a)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    ∃ σ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ≃+* ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (a ^ q) ((a ^ q) ^ q)),
      (∀ (g : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) (hgF : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar (1 * q)),
          ((σ g : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (a ^ q) ((a ^ q) ^ q))) : LaurentSeries (AlgebraicClosure ℚ))
            = ((frickeInvolutionBar (1 * q) ⟨(g : LaurentSeries (AlgebraicClosure ℚ)), hgF⟩ : modularFunctionFieldBar (1 * q)) :
                LaurentSeries (AlgebraicClosure ℚ))) ∧
      (∀ p : MvPolynomial (Fin 2) ↥(coeffSubring A K),
          σ (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) p)
            = modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) (a ^ q) ((a ^ q) ^ q)
                (MvPolynomial.rename (Equiv.swap 0 1) p)) := by sorry
