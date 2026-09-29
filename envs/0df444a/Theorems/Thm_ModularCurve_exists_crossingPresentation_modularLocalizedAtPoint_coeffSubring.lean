-- Prove2me | Theorems.Thm_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring
-- name    : ModularCurve.exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/54db7dc5-f796-5d29-afa7-72809229ee35
-- title:
--   Crossing presentation at a supersingular node of X₀(q)
-- statement:
--   Let $q\ge 5$ be a prime, $A$ a valuation subring of $\overline{\mathbb Q}$, $k$ a field of characteristic $q$, and $\mathrm{red}\colon A\to k$ a ring homomorphism. Let $a\in k$ satisfy $a^{q^2}=a$ and lie in `ssJSet q k`, i.e. every Weierstrass curve over $k$ that is elliptic and has $j$-invariant $a$ has no nonzero affine point killed by $q$. Let $K\subseteq\overline{\mathbb Q}$ be a number field, write $A_K=$ `coeffSubring A K` $=A\cap K$ and let `redRestrict red K` be the restriction of $\mathrm{red}$ to $A_K$; assume $x\in A_K$ reduces to $a$, and that $\varpi\in A_K$ generates the kernel in the divisibility sense: $c$ reduces to $0$ iff $\varpi\mid c$. Put $R=$ `modularLocalizedAtPoint (1*q) A_K (redRestrict red K) a (a^q)`, the subring of Laurent series over $\overline{\mathbb Q}$ consisting of the $f$ with $f\cdot \mathrm{mev}(s)=\mathrm{mev}(r)$ for some $r,s\in A_K[X_0,X_1]$ whose value $s(a,a^q)$ under reduction is nonzero, where $\mathrm{mev}$ sends $X_0,X_1$ to the $q$-expansions $j$ and $j$ at level $1\cdot q$ and constants to constant series. Then there are $e_K\ge 1$ and a unit $\varepsilon\in A_K$ with $q=\varpi^{e_K}\varepsilon$, and elements $G',H',w\in R$ with $w$ a unit, such that, writing $P=\mathrm{mev}(\varpi)\in R$: $G'H'=P^{\,\mathrm{jWidth}(a)\,e_K}w$, where $\mathrm{jWidth}(a)=3,2,1$ according as $a=0$, $a=1728$, or neither; for every local-ring structure on $R$ its maximal ideal is $(P,G',H')$; the ideals $(P,G')$ and $(P,H')$ are prime, with $H'\notin(P,G')$ and $G'\notin(P,H')$; and $(P,G')=(P,\mathrm{mev}(X_1-X_0^q))$, $(P,H')=(P,\mathrm{mev}(X_0-X_1^q))$.
--
--   This supplies, over the ring of coefficients $A\cap K$ of a number field $K$, the local data of the supersingular crossing point of $X_0(q)$ in characteristic $q$ — two branches meeting with thickness $\mathrm{jWidth}(a)\,e_K$, the branches being cut out modulo $\varpi$ by $j_q-j^q$ and $j-j_q^{\,q}$ — in exactly the form required by the crossing-presentation criterion for normality. It is used by the two-branch normalisation statements at widths corresponding to $a=0$ and $a=1728$ and by the computation of the crossing exponent as width times place exponent.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring.lean

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

open ModularCurve
open IsLocalRing
open ModularCurve.NodeLocalized

theorem ModularCurve.exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (hq : 5 ≤ q)
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
