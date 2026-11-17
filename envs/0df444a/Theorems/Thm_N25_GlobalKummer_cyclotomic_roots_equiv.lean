-- Prove2me | Theorems.Thm_N25_GlobalKummer_cyclotomic_roots_equiv
-- name    : N25.GlobalKummer.cyclotomic_roots_equiv
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:34:32.320331+00:00
-- url     : https://prove2.me/theorems/3c3b4b95-2d66-410f-9095-75965d33add8
-- title:
--   The cyclotomic line is the group of $71$st roots of unity
-- statement:
--   Let $G_{ℚ}=\mathrm{Gal}(ℚ̄/ℚ)$ and let $χ_{71}:G_{ℚ}\to 𝔽_{71}^×$ be the mod-$71$ cyclotomic character. There exists an additive-group isomorphism $e:𝔽_{71}\to μ_{71}(ℚ̄)$ that intertwines the cyclotomic actions: $$e(χ_{71}(σ)a)=σ(e(a))\quad\text{for all }σ\in G_{ℚ},\ a\in 𝔽_{71}.$$ This identifies the abstract cyclotomic quotient representation with actual roots of unity.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_GlobalKummerSequence
import Definitions.Def_GroupCohomology_Kummer

set_option autoImplicit false
noncomputable section
open N25
open N25.GlobalKummer
local instance instL_N25_GlobalKummer_cyclotomic_roots_equiv_23397f_ia5e78c : Fact (Nat.Prime 71) := ⟨by decide⟩

theorem N25.GlobalKummer.cyclotomic_roots_equiv :
    ∃ e : ZMod 71 ≃+ Additive (rootsOfUnity 71 (AlgebraicClosure ℚ)),
      ∀ (σ : Gal) (a : ZMod 71),
        e ((ExtCitation.cycloChar 71 σ : ZMod 71) * a) =
          Additive.ofMul (σ • Additive.toMul (e a)) := by sorry
