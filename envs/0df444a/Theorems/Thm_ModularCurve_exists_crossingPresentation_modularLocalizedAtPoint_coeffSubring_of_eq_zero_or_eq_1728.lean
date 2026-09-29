-- Prove2me | Theorems.Thm_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728
-- name    : ModularCurve.exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/c5cad66d-23e6-5d7f-9ab3-679bc265692a
-- title:
--   Crossing presentation of the node ring at j=0 or 1728
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red}\colon A\to k$. Let $a\in k$ lie in `ssJSet q k`, i.e. every elliptic Weierstrass curve over $k$ with $j$-invariant $a$ has no nonzero affine point killed by $q$, and assume $a^{q^2}=a$, $q\ge 5$ and $a=0$ or $a=1728$. Let $K$ be a finite extension of $\mathbb Q$ inside $\overline{\mathbb Q}$, put $A_0=\mathrm{coeffSubring}\,A\,K=A\cap K$ with reduction $\mathrm{redRestrict}$ the restriction of $\mathrm{red}$ to $A_0$, let $x\in A_0$ reduce to $a$, and let $\varpi\in A_0$ be such that an element of $A_0$ reduces to $0$ exactly when it is a multiple of $\varpi$. Write $R$ for `modularLocalizedAtPoint (1 * q) A₀ (redRestrict red K) a (a ^ q)`: the subring of Laurent series over $\overline{\mathbb Q}$ consisting of those $f$ admitting $r,s\in A_0[X_0,X_1]$ with $s(a,a^q)\ne 0$ (after reduction of coefficients) and $f\cdot s(j,j_{1\cdot q})=r(j,j_{1\cdot q})$, where $X_0,X_1$ are evaluated at the $q$-expansions $j$ and its $N$-fold expansion for $N=1\cdot q$, and constants via the inclusion of $A_0$. The assertion is that there exist $e_K\ge 1$ and a unit $\varepsilon\in A_0$ with $q=\varpi^{e_K}\varepsilon$, and elements $G',H',w\in R$ with $w$ a unit, such that, writing $\Pi\in R$ for the constant series $\varpi$, one has $G'H'=\Pi^{\,\mathrm{jWidth}(a)\cdot e_K}\,w$ with $\mathrm{jWidth}(a)=3$ for $a=0$ and $2$ for $a=1728$; moreover, whenever $R$ is local, its maximal ideal is $(\Pi,G',H')$; the ideals $(\Pi,G')$ and $(\Pi,H')$ are prime; $H'\notin(\Pi,G')$ and $G'\notin(\Pi,H')$; and the two branches are pinned by $(\Pi,G')=(\Pi,\,j_{1\cdot q}-j^{\,q})$ and $(\Pi,H')=(\Pi,\,j-j_{1\cdot q}^{\,q})$.
--
--   This is the wide-node case of the Deligne–Rapoport/Mazur–Rapoport description of $X_0(q)$ in characteristic $q$ at a supersingular point with extra automorphisms, where the local intersection multiplicity of the two branches is $\mathrm{jWidth}(a)\in\{2,3\}$ rather than $1$. Together with the width-one and the inert-quadratic variants it feeds the uniform crossing presentation [`ModularCurve.exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring`](thm.html#ModularCurve.exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring) and, through it, the two-branch normalisation and place-specialisation results used later.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open IsLocalRing ModularCurve
open ModularCurve.NodeLocalized

theorem ModularCurve.exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (hq : 5 ≤ q) (h01728 : a = 0 ∨ a = 1728)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a)
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d) :
    ∃ (eK : ℕ) (ε : ↥(coeffSubring A K)), 1 ≤ eK ∧ IsUnit ε ∧ ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ eK * ε ∧
    ∃ (G' H' w : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
      IsUnit w ∧
      G' * H' = (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ^ (jWidth a * eK) * w ∧
      (∀ [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))],
        IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) =
          Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G', H'}) ∧
      (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G'}).IsPrime ∧
      (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), H'}).IsPrime ∧
      H' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G'} ∧
      G' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), H'} ∧
      Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G'} = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))} ∧
      Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), H'} = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))} := by sorry
