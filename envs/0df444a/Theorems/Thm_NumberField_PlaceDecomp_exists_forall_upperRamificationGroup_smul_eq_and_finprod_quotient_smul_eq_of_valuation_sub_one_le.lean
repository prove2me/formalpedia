-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_exists_forall_upperRamificationGroup_smul_eq_and_finprod_quotient_smul_eq_of_valuation_sub_one_le
-- name    : NumberField.PlaceDecomp.exists_forall_upperRamificationGroup_smul_eq_and_finprod_quotient_smul_eq_of_valuation_sub_one_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/d675872e-e0c9-59dd-b6d4-bf243c7fe5be
-- title:
--   Level-n units of Eᵥ are norms from the Gⁿ layer
-- statement:
--   Let $E$ and $F$ be number fields with $F$ an algebra over $E$ such that $F/E$ is Galois and the Galois group $F \simeq_{\mathrm{alg}[E]} F$ is commutative. Let $v$ be a height one prime of $\mathcal O_E$, let $w$ be a height one prime of $\mathcal O_F$ whose pullback to $\mathcal O_E$ is $v$, and let $n$ be a natural number. Let $a$ be a unit of the $v$-adic completion $E_v$ with $\mathrm{Val}(a) = 1$ and $\mathrm{Val}(a - 1) \le \exp(-n)$ in the value group written multiplicatively via `WithZero.exp`. Then there is an element $b$ of the $w$-adic completion $F_w$ with the following two properties. First, $b$ is fixed by every element of [`ValuationSubring.upperRamificationGroup`](def/Mathlib_RingTheory_Valuation_UpperRamificationGroup.html#L261) of the valuation subring $A$ of the $w$-adic valuation of $F$ at the rational parameter $n$; by definition this is the subgroup of the decomposition subgroup of $A$ over $E$ given by the lower ramification group at index $i$, i.e. the inertia subgroup of $\mathfrak m_A^{\,i+1}$, where $i$ is the least natural number with $n \le$ `herbrandPhi` at $i$. Second, writing $D$ for the decomposition subgroup of $A$ over $E$ (the group `decomp E F w`), the finite product over the cosets $c$ in the quotient of $D$ by that upper ramification subgroup of $(\mathrm{Quotient.out}\,c) \cdot b$ equals the image of $a$ under the semialgebra map [`IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom`](def/DedekindDomain_Completion_BaseChange.html#L425) from $E_v$ to $F_w$ over $\mathrm{algebraMap}\ E\ F$ attached to the extension $\langle w, hw\rangle$ of $v$.
--
--   This is the local class field theory statement that a unit of $E_v$ congruent to $1$ modulo level $n$ is a norm from the layer of $F_w$ cut out by the $n$-th upper ramification group, the product over coset representatives being the relative norm of that layer by the fixedness clause. It is used in the proof that the idelic Artin map carries the level-$n$ units into the $n$-th upper ramification group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_exists_forall_upperRamificationGroup_smul_eq_and_finprod_quotient_smul_eq_of_valuation_sub_one_le.lean

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.exists_forall_upperRamificationGroup_smul_eq_and_finprod_quotient_smul_eq_of_valuation_sub_one_le
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsMulCommutative (F ≃ₐ[E] F)]
    (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 F)) (hw : w.under (𝓞 E) = v) (n : ℕ)
    (a : (v.adicCompletion E)ˣ) (ha : Valued.v (a : v.adicCompletion E) = 1)
    (han : Valued.v ((a : v.adicCompletion E) - 1) ≤ WithZero.exp (-(n : ℤ))) :
    ∃ b : w.adicCompletion F,
      (∀ h ∈ ValuationSubring.upperRamificationGroup E ((w.valuation F).valuationSubring) (n : ℚ), h • b = b) ∧
      (∏ᶠ c : ↥(NumberField.PlaceDecomp.decomp E F w) ⧸
          ValuationSubring.upperRamificationGroup E ((w.valuation F).valuationSubring) (n : ℚ),
        (Quotient.out c) • b) =
        IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F (⟨w, hw⟩ : v.Extension (𝓞 F))
          (a : v.adicCompletion E) := by sorry
