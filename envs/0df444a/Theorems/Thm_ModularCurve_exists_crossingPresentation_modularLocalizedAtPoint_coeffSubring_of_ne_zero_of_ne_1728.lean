-- Prove2me | Theorems.Thm_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_ne_zero_of_ne_1728
-- name    : ModularCurve.exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_ne_zero_of_ne_1728
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/5b26bb5e-8fe0-5f3b-885c-2badf4cff35e
-- title:
--   Crossing presentation of the node ring at a width-one supersingular point
-- statement:
--   Let $q$ be a prime with $q \ge 5$, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$, let $k$ be a field of characteristic $q$ and let $\mathrm{red} \colon A \to k$ be a ring homomorphism. Let $a \in k$ lie in `ssJSet q k`, i.e. every elliptic Weierstrass curve over $k$ with $j$-invariant $a$ has no nonzero affine point killed by $q$, and assume $a^{q^2} = a$, $a \ne 0$ and $a \ne 1728$. Let $K$ be an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$ of finite degree over $\mathbb{Q}$ and put $A_0 = A \cap K$ (`coeffSubring A K`), with reduction $\mathrm{red}_0 \colon A_0 \to k$ obtained by restricting $\mathrm{red}$. Assume given $x \in A_0$ with $\mathrm{red}_0(x) = a$, and $\varpi \in A_0$ such that $\mathrm{red}_0(c) = 0$ holds exactly when $c$ is a multiple of $\varpi$. Let $R_0$ be the subring `modularLocalizedAtPoint (1 * q) A₀ red₀ a (a ^ q)` of $\mathrm{LaurentSeries}(\overline{\mathbb{Q}})$, consisting of those Laurent series $f$ for which there are $r, s \in A_0[X_0, X_1]$ with $s(a, a^q) \ne 0$ after reduction along $\mathrm{red}_0$ and $f \cdot \mathrm{ev}(s) = \mathrm{ev}(r)$, where $\mathrm{ev}$ substitutes the $q$-expansions $X_0 \mapsto j$, $X_1 \mapsto j \circ (q\text{-expansion scaling by } 1 \cdot q)$ and maps coefficients by the inclusion $A_0 \subseteq \overline{\mathbb{Q}}$. Write $\Pi \in R_0$ for the image of the constant polynomial $\varpi$ under $\mathrm{ev}$. The conclusion asserts the existence of $e_K \in \mathbb{N}$ and $\varepsilon \in A_0$ with $e_K \ge 1$, $\varepsilon$ a unit and $q = \varpi^{e_K}\varepsilon$ in $A_0$, and of $G', H', w \in R_0$ with $w$ a unit such that: $G' H' = \Pi^{\,\mathrm{jWidth}(a)\, e_K} w$, where $\mathrm{jWidth}(a) = 1$ because $a \ne 0, 1728$; for any local-ring structure on $R_0$ its maximal ideal is $(\Pi, G', H')$; the ideals $(\Pi, G')$ and $(\Pi, H')$ are prime; $H' \notin (\Pi, G')$ and $G' \notin (\Pi, H')$; and $(\Pi, G') = (\Pi, \mathrm{ev}(X_1 - X_0^q))$, $(\Pi, H') = (\Pi, \mathrm{ev}(X_0 - X_1^q))$.
--
--   This is the width-one case ($a \notin \{0, 1728\}$) of the local description of the modular curve $X_0(q)$ at a supersingular point of its characteristic-$q$ fibre: the descended node ring has an ordinary double point presentation $G'H' = \varpi^{e_K} \cdot \mathrm{unit}$, with the two branches cut out by the congruences $j_q \equiv j^q$ and $j \equiv j_q^{\,q}$. It feeds the statement covering all widths, [`ModularCurve.exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring`](thm.html#ModularCurve.exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_ne_zero_of_ne_1728.lean

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

theorem ModularCurve.exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_ne_zero_of_ne_1728
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (hq : 5 ≤ q) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
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
