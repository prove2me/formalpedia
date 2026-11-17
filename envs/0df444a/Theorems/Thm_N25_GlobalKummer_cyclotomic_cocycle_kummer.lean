-- Prove2me | Theorems.Thm_N25_GlobalKummer_cyclotomic_cocycle_kummer
-- name    : N25.GlobalKummer.cyclotomic_cocycle_kummer
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:33:55.832539+00:00
-- url     : https://prove2.me/theorems/ddc5fa95-6b74-4296-a582-c8f96867c486
-- title:
--   Cyclotomic cocycles are rational Kummer cocycles
-- statement:
--   Let $G_{ℚ}=\mathrm{Gal}(ℚ̄/ℚ)$, let $𝔽_{71}(χ_{71})$ be the one-dimensional representation defined by the mod-$71$ cyclotomic character, and let $c\in Z^1(G_{ℚ},𝔽_{71}(χ_{71}))$ be a cocycle that factors through a finite quotient. Then there are a $G_{ℚ}$-equivariant additive isomorphism $e:𝔽_{71}\to μ_{71}(ℚ̄)$, a rational unit $a\in ℚ^×$, and $α\in ℚ̄^×$ such that, for all $σ\in G_{ℚ}$ and $b\in 𝔽_{71}$, $$e(χ_{71}(σ)b)=σ(e(b)),\qquad α^{71}=a,\qquad e(c(σ))=σ(α)/α.$$ This realizes the cyclotomic quotient of the division class by explicit rational Kummer data. Formalization note: the finite-level hypothesis is Lean's continuity witness for the cocycle.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_GlobalKummerSequence
import Definitions.Def_GroupCohomology_Kummer
import Theorems.Thm_groupCohomology_Kummer_exists_kummerCocycle_eq_of_isMulCocycle1_of_level

set_option autoImplicit false
noncomputable section
open N25
open N25.GlobalKummer
local instance instL_N25_GlobalKummer_cyclotomic_cocycle_kumm_23397f_ie26115 : Fact (Nat.Prime 71) := ⟨by decide⟩

theorem N25.GlobalKummer.cyclotomic_cocycle_kummer
    (c : groupCohomology.cocycles₁ cyclotomicRep)
    (hc : groupCohomology.IsLevelConstant₁ (MonoidHom.id Gal) c) :
    ∃ (e : ZMod 71 ≃+ Additive (rootsOfUnity 71 (AlgebraicClosure ℚ)))
      (a : ℚˣ) (α : (AlgebraicClosure ℚ)ˣ),
      (∀ (σ : Gal) (b : ZMod 71),
        e ((ExtCitation.cycloChar 71 σ : ZMod 71) * b) =
          Additive.ofMul (σ • Additive.toMul (e b))) ∧
      algebraMap ℚ (AlgebraicClosure ℚ) (a : ℚ) = (α : AlgebraicClosure ℚ) ^ 71 ∧
      ∀ σ : Gal, (Additive.toMul (e (c σ))).val =
        groupCohomology.Kummer.kummerCocycle α σ := by sorry
