-- Prove2me | Theorems.Thm_ModularCurve_exists_place_restrictAlong_heckeAlphaBar_eq_and_hasValue_tInfty
-- name    : ModularCurve.exists_place_restrictAlong_heckeAlphaBar_eq_and_hasValue_tInfty
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/eff83df4-e40d-5a43-bb5f-ea4771f4ea65
-- title:
--   A place of X₀(Nq) above a cusp where t_∞ reduces to 1
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, a natural number $N \neq 0$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$. Fix further `data`, a monic bivariate integral polynomial $\Phi$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$ of $q$-expansions, together with the hypothesis `hKr` that its reduction modulo $q$ equals $(C(X)^q - X)(C(X) - X^q)$ (Kronecker's congruence), the hypothesis `hα` that the degeneracy inclusion `heckeAlphaBar` of the base-changed full modular function field of level $N$ into that of level $Nq$ inside $\overline{\mathbb{Q}}((t))$ is integral as a ring map, and the hypothesis $q \nmid N$. Let $w$ be a place of `modularFunctionFieldBar N` over $\overline{\mathbb{Q}}$ — a proper valuation subring containing the constants and having principal ideals — such that $\operatorname{ord}_w(j - a) \le 0$ for every $a \in A$, where $j$ is the coefficientwise image of the Laurent series `jq`. Then there is a place $c$ of `modularFunctionFieldBar (N * q)` whose restriction along `heckeAlphaBar` is $w$, and an element $\tau \in A$ with $\mathrm{red}\,\tau = 1$ such that $t_\infty = j_Q / j^q$ lies in the valuation subring of $c$ and has residue the image of $\tau$.
--
--   This is the Hensel-type existence statement at a cusp: over a place $w$ of the level-$N$ modular function field at which $j$ takes no $A$-integral value, the modular equation in Kronecker's congruence form has a simple root producing a place of level $Nq$ lying over $w$ along the degeneracy map, normalised by the requirement that the Atkin–Lehner coordinate $t_\infty = j_Q/j^q$ specialises to $1$. It feeds the construction of common unit poles for the regular prolongations attached to a place specialisation in characteristic $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_place_restrictAlong_heckeAlphaBar_eq_and_hasValue_tInfty.lean

import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.exists_place_restrictAlong_heckeAlphaBar_eq_and_hasValue_tInfty
    (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N]
    (k : Type) [Field k] [CharP k q] (red : A →+* k)
    (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q) (hqN : ¬ q ∣ N)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hw : ∀ a : A, w.ord
        ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) ≤ 0) :
    ∃ c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      c.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα = w ∧
      ∃ τ : A, red τ = 1 ∧ c.HasValue (tInfty N q) (τ : AlgebraicClosure ℚ) := by sorry
