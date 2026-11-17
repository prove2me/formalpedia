-- Prove2me | Theorems.Thm_N25_GlobalKummer_cyclotomic_coboundary_of_valuations
-- name    : N25.GlobalKummer.cyclotomic_coboundary_of_valuations
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:01:55.232461+00:00
-- url     : https://prove2.me/theorems/0494899e-5206-4cec-912d-230fae7be2d3
-- title:
--   Valuation-divisible cyclotomic Kummer classes vanish
-- statement:
--   Let $G=\operatorname{Gal}(\overline{\mathbf Q}/\mathbf Q)$ and let $c:G\to\mathbf F_{71}(\chi_{71})$ be a one-cocycle. Let $e:\mathbf F_{71}\to\mu_{71}(\overline{\mathbf Q})$ be an additive-group isomorphism compatible with Galois action, so $e(\chi_{71}(\sigma)u)=\sigma(e(u))$. Let $a\in\mathbf Q^\times$ and $\alpha\in\overline{\mathbf Q}^{\times}$ satisfy $a=\alpha^{71}$ in $\overline{\mathbf Q}$, and assume the root of unity corresponding to $c(\sigma)$ is the Kummer cocycle $\sigma(\alpha)/\alpha$ for every $\sigma\in G$. If $71$ divides the $p$-adic valuation $v_p(a)$ for every rational prime $p$, then
--
--   $$\exists m\in\mathbf F_{71}(\chi_{71})\ \forall\sigma\in G,\quad c(\sigma)=\sigma m-m,\qquad [c]=0\text{ in }H^1(G,\mathbf F_{71}(\chi_{71})).$$
--
--   This kills the cyclotomic quotient class in the global Kummer descent. Formalization note: the theorem records the root-of-unity group additively and uses explicit coercions between additive and multiplicative notation.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_GlobalKummerSequence
import Definitions.Def_GroupCohomology_Kummer
import Theorems.Thm_groupCohomology_Kummer_exists_kummerCocycle_eq_of_isMulCocycle1_of_level

set_option autoImplicit false
noncomputable section
open N25
open N25.GlobalKummer
local instance rationalValuationPrimeSeventyOne_i03ec08 : Fact (Nat.Prime 71) := ⟨by decide⟩

theorem N25.GlobalKummer.cyclotomic_coboundary_of_valuations
    (c : groupCohomology.cocycles₁ cyclotomicRep)
    (e : ZMod 71 ≃+ Additive (rootsOfUnity 71 (AlgebraicClosure ℚ)))
    (he : ∀ (σ : Gal) (a : ZMod 71),
      e ((ExtCitation.cycloChar 71 σ : ZMod 71) * a) =
        Additive.ofMul (σ • Additive.toMul (e a)))
    (a : ℚˣ) (α : (AlgebraicClosure ℚ)ˣ)
    (hα : algebraMap ℚ (AlgebraicClosure ℚ) (a : ℚ) = (α : AlgebraicClosure ℚ) ^ 71)
    (hc : ∀ σ : Gal, (Additive.toMul (e (c σ))).val =
      groupCohomology.Kummer.kummerCocycle α σ)
    (hval : ∀ p : ℕ, Nat.Prime p → (71 : ℤ) ∣ padicValRat p (a : ℚ)) :
    (∃ m : cyclotomicRep, ∀ σ : Gal, c σ = cyclotomicRep.ρ σ m - m) ∧
      groupCohomology.H1π cyclotomicRep c = 0 := by sorry
