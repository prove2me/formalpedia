-- Prove2me | Theorems.Thm_ModularCurve_exists_place_restrictAlong_heckeBetaBar_eq_and_hasValue_tZero
-- name    : ModularCurve.exists_place_restrictAlong_heckeBetaBar_eq_and_hasValue_tZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/9385a99b-6899-5ec9-94b5-68a447ff2fe5
-- title:
--   A place above w along β where t₀ reduces to 1
-- statement:
--   Let $q$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb Q}$, let $N$ be a nonzero natural number, let $k$ be a field of characteristic $q$ and let $\mathrm{red} : A \to k$ be a ring homomorphism. Let `data` consist of a monic polynomial $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ in $Y$ annihilating the $q$-expansion pair $(j, j_q)$, and assume Kronecker's congruence for it, namely that the reduction of $\Phi$ modulo $q$ equals $(C(X)^q - X)(C(X) - X^q)$; assume further that the degeneracy algebra map $\beta$ from $\overline{\mathbb Q}$-base-changed Laurent-series function field of level $N$ to that of level $Nq$ is integral as a ring homomorphism, and that $q \nmid N$. Finally let $w$ be a place of the level-$N$ field over $\overline{\mathbb Q}$ (a proper valuation subring containing the base field and a principal ideal ring) such that for every $a \in A$ the order $w.\mathrm{ord}(j - a) \le 0$, where $j$ denotes the element given by the $q$-expansion `jq` with coefficients pushed into $\overline{\mathbb Q}$. Then there is a place $c$ of the level-$Nq$ field over $\overline{\mathbb Q}$ whose restriction along $\beta$ is $w$, together with $\tau \in A$ such that $\mathrm{red}(\tau) = 1$ and $t_0 = j/j_q^{\,q}$ lies in the valuation ring of $c$ with residue the image of $\tau$ in the residue field of $c$.
--
--   This is the local analysis at a cusp of $X_0(N)$: the hypothesis on $w$ says that $j$ has a pole there, and Kronecker's congruence for the modular equation provides, by a Hensel-type argument, one unramified place of $X_0(Nq)$ above it at which the ratio $t_0 = j/j_q^{\,q}$ is an $A$-adic unit congruent to $1$. It is used in the prolongation-tuple arguments that produce common units with prescribed poles for the two regular prolongations attached to a place specialisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_place_restrictAlong_heckeBetaBar_eq_and_hasValue_tZero.lean

import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.exists_place_restrictAlong_heckeBetaBar_eq_and_hasValue_tZero
    (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N]
    (k : Type) [Field k] [CharP k q] (red : A →+* k)
    (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q) (hqN : ¬ q ∣ N)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hw : ∀ a : A, w.ord
        ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) ≤ 0) :
    ∃ c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      c.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ = w ∧
      ∃ τ : A, red τ = 1 ∧ c.HasValue (tZero N q) (τ : AlgebraicClosure ℚ) := by sorry
