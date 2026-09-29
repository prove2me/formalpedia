-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_forall_exists_finprod_smul_eq_and_of_ramificationIdx_eq_one
-- name    : NumberField.PlaceDecomp.forall_exists_finprod_smul_eq_and_of_ramificationIdx_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/8ffb4a9d-d1e0-5c94-a9d6-d5648f2ab75b
-- title:
--   Local norm onto higher units at an unramified place
-- statement:
--   Let $E$ and $F$ be number fields with $F$ an extension of $E$ that is Galois, let $v$ be a nonzero prime of $\mathcal O_E$ and $w$ a nonzero prime of $\mathcal O_F$ lying over $v$ (i.e. `w.under (𝓞 E) = v`), and assume the ramification index of $w$ over $v$ is $1$. Fix $m \in \mathbb N$, and call a unit $u$ of a completion *$m$-close to $1$* when its valuation is $1$ and, unless $m = 0$, $\mathrm{v}(u - 1) \le \exp(-m)$ in the multiplicatively written value group. Write $D_w =$ `decomp E F w` for the decomposition subgroup of $F \simeq_E F$ attached to the valuation subring of the $w$-adic valuation of $F$, and let $\iota$ be the semialgebra map `adicCompletionSemialgHom` from $E_v$ to $F_w$ over $E \to F$. The theorem asserts the conjunction of two statements: for every unit $b$ of $F_w$ that is $m$-close to $1$ there is a unit $a$ of $E_v$ that is $m$-close to $1$ with $\prod^{\mathrm f}_{\sigma \in D_w} \sigma \cdot b = \iota(a)$ in $F_w$; and conversely, for every unit $a$ of $E_v$ that is $m$-close to $1$ there is a unit $b$ of $F_w$ that is $m$-close to $1$ satisfying the same equation.
--
--   This is the classical statement that in an unramified extension of local fields the norm maps the $m$-th higher unit group onto the $m$-th higher unit group of the base, here packaged in the form of a two-way surjectivity between unit groups of the completions $F_w$ and $E_v$, with the local norm presented as the finite product over the decomposition group. It feeds the construction of compatible Galois-equivariant choices of units used downstream at [`NumberField.PlaceDecomp.exists_forall_upperRamificationGroup_smul_eq_and_finprod_quotient_smul_eq_of_valuation_sub_one_le`](thm.html#NumberField.PlaceDecomp.exists_forall_upperRamificationGroup_smul_eq_and_finprod_quotient_smul_eq_of_valuation_sub_one_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_forall_exists_finprod_smul_eq_and_of_ramificationIdx_eq_one.lean

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.forall_exists_finprod_smul_eq_and_of_ramificationIdx_eq_one
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 F)) (hw : w.under (𝓞 E) = v)
    (he : v.asIdeal.ramificationIdx' w.asIdeal = 1) (m : ℕ) :
    (∀ b : (w.adicCompletion F)ˣ, Valued.v (b : w.adicCompletion F) = 1 →
        (m = 0 ∨ Valued.v ((b : w.adicCompletion F) - 1) ≤ WithZero.exp (-(m : ℤ))) →
        ∃ a : (v.adicCompletion E)ˣ, Valued.v (a : v.adicCompletion E) = 1 ∧
          (m = 0 ∨ Valued.v ((a : v.adicCompletion E) - 1) ≤ WithZero.exp (-(m : ℤ))) ∧
          (((∏ᶠ σ : ↥(NumberField.PlaceDecomp.decomp E F w), σ • b : (w.adicCompletion F)ˣ) : (w.adicCompletion F)ˣ) :
              w.adicCompletion F) =
            IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F (⟨w, hw⟩ : v.Extension (𝓞 F))
              (a : v.adicCompletion E)) ∧
    (∀ a : (v.adicCompletion E)ˣ, Valued.v (a : v.adicCompletion E) = 1 →
        (m = 0 ∨ Valued.v ((a : v.adicCompletion E) - 1) ≤ WithZero.exp (-(m : ℤ))) →
        ∃ b : (w.adicCompletion F)ˣ, Valued.v (b : w.adicCompletion F) = 1 ∧
          (m = 0 ∨ Valued.v ((b : w.adicCompletion F) - 1) ≤ WithZero.exp (-(m : ℤ))) ∧
          (((∏ᶠ σ : ↥(NumberField.PlaceDecomp.decomp E F w), σ • b : (w.adicCompletion F)ˣ) : (w.adicCompletion F)ˣ) :
              w.adicCompletion F) =
            IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F (⟨w, hw⟩ : v.Extension (𝓞 F))
              (a : v.adicCompletion E)) := by sorry
