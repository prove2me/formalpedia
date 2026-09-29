-- Prove2me | Theorems.Thm_ModularCurve_NodeLocalized_isPrime_span_uniformizer_branches_modularLocalizedAtPoint
-- name    : ModularCurve.NodeLocalized.isPrime_span_uniformizer_branches_modularLocalizedAtPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/964a247c-f852-5ee6-873b-9c686841a694
-- title:
--   Branch ideals at a point of the special fibre are prime
-- statement:
--   Let $q$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb Q}$, let $k$ be a field of characteristic $q$, let $\mathrm{red}\colon A \to k$ be a ring homomorphism and let $a \in k$. Let $K$ be a finite extension of $\mathbb Q$ inside $\overline{\mathbb Q}$, and write $A_0 = A \cap K$ for `coeffSubring A K`, with $\mathrm{red}_0 =$ `redRestrict red K` the restriction of $\mathrm{red}$ to $A_0$. Let $\varpi \in A_0$ be such that for every $c \in A_0$ one has $\mathrm{red}_0(c) = 0$ if and only if $c = \varpi d$ for some $d \in A_0$, i.e. $\ker \mathrm{red}_0 = \varpi A_0$. Work in the ring $R_0 =$ `modularLocalizedAtPoint (1 * q) A_0 red_0 a (a ^ q)`, the subring of Laurent series over $\overline{\mathbb Q}$ consisting of those $f$ for which there are $r, s \in A_0[X_0, X_1]$ with $s$ not vanishing at $(a, a^q)$ after applying $\mathrm{red}_0$ to its coefficients and $f \cdot \mathrm{ev}(s) = \mathrm{ev}(r)$, where $\mathrm{ev} =$ `modularEval (1 * q)` sends $X_0$ to the $q$-expansion `jqModC` of $j$, $X_1$ to `jqNModC` for $N = 1 \cdot q$, and constants to constant series. Put $P = \mathrm{ev}(\varpi) \in R_0$, $G = \mathrm{ev}(X_1 - X_0^q)$ and $H = \mathrm{ev}(X_0 - X_1^q)$. The conclusion is: the ideal $(P, G)$ of $R_0$ is prime, $H \notin (P,G)$, and $\mathrm{ev}(X_0 - c) \notin (P,G)$ for every $c \in A_0$; and, if moreover $a^{q^2} = a$, the ideal $(P, H)$ is prime and $G \notin (P,H)$.
--
--   This identifies the branches of the special fibre of the plane model of $X_0(q)$ through the point $(a, a^q)$, in accordance with Kronecker's congruence $\Phi_q \equiv (X_0^q - X_1)(X_0 - X_1^q) \bmod q$: the branch $j_q = j^q$ always passes through such a point, while the branch $j = j_q^q$ does so exactly when $a$ lies in the subfield cut out by $a^{q^2} = a$, which is why the second clause is conditional. It feeds the construction of height-one primes attached to crossing parameters and the analysis of $R_0$ as a Noetherian local ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_NodeLocalized_isPrime_span_uniformizer_branches_modularLocalizedAtPoint.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.NodeLocalized

theorem ModularCurve.NodeLocalized.isPrime_span_uniformizer_branches_modularLocalizedAtPoint
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k) (a : k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d) :
    ((Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
        (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))}).IsPrime ∧
      (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
        ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
            (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))} ∧
      ∀ c : ↥(coeffSubring A K), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.C c),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
        ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
            (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))}) ∧
    (a ^ (q ^ 2) = a →
      (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
          (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))}).IsPrime ∧
      (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
        ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
            (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))}) := by sorry
