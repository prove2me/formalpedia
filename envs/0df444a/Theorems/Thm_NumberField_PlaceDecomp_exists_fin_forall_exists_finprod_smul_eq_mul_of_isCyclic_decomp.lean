-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_exists_fin_forall_exists_finprod_smul_eq_mul_of_isCyclic_decomp
-- name    : NumberField.PlaceDecomp.exists_fin_forall_exists_finprod_smul_eq_mul_of_isCyclic_decomp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/3fe0f7c4-2647-5dae-803a-7e38fd04c34b
-- title:
--   Cyclic decomposition group: local norm index at most |D_w|
-- statement:
--   Let $E$ and $F$ be number fields with $F$ an extension of $E$ that is Galois, let $v$ be a height-one prime of the ring of integers $\mathcal{O}_E$ and $w$ a height-one prime of $\mathcal{O}_F$ with $w$ lying over $v$, i.e. $w$ contracts to $v$ along $\mathcal{O}_E \to \mathcal{O}_F$, and write $D_w =$ [`NumberField.PlaceDecomp.decomp E F w`](def/NumberField_PlaceDecompositionAction.html#L82) for the decomposition subgroup of $F \simeq_{\mathrm{alg}[E]} F$ attached to the valuation subring of the $w$-adic valuation of $F$; assume $D_w$ is cyclic. The assertion is that there exist a natural number $n$ and a family $c : \mathrm{Fin}\, n \to (E_v)^\times$ of units of the $v$-adic completion $E_v$ such that $n \le \#D_w$ and such that for every unit $a$ of $E_v$ there are an index $i$ and a unit $b$ of the $w$-adic completion $F_w$ with $\prod^{f}_{\sigma \in D_w} \sigma \cdot b$, computed as a finprod of units of $F_w$ over the subgroup $D_w$ acting on $F_w$ and then viewed in $F_w$, equal to the image of the unit $a\,c_i^{-1}$ of $E_v$ under the semialgebra map [`IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom`](def/DedekindDomain_Completion_BaseChange.html#L425) from $E_v$ to $F_w$ associated with the extension $w \mid v$. Thus at most $\#D_w$ elements of $E_v^\times$ suffice as coset representatives for the subgroup of norms from $F_w^\times$.
--
--   This is the cyclic case of the local norm index bound $[E_v^\times : N_{F_w/E_v} F_w^\times] \le \#D_w$, packaged as an explicit finite list of representatives for the cosets of the group of norms rather than as an index statement. It is used to deduce the corresponding bound when the decomposition group is only assumed commutative, in [`NumberField.PlaceDecomp.exists_fin_forall_exists_finprod_smul_eq_mul_of_isMulCommutative_decomp`](thm.html#NumberField.PlaceDecomp.exists_fin_forall_exists_finprod_smul_eq_mul_of_isMulCommutative_decomp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_exists_fin_forall_exists_finprod_smul_eq_mul_of_isCyclic_decomp.lean

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

theorem NumberField.PlaceDecomp.exists_fin_forall_exists_finprod_smul_eq_mul_of_isCyclic_decomp
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 F)) (hw : w.under (𝓞 E) = v)
    [IsCyclic ↥(NumberField.PlaceDecomp.decomp E F w)] :
    ∃ (n : ℕ) (c : Fin n → (v.adicCompletion E)ˣ), n ≤ Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) ∧
      ∀ a : (v.adicCompletion E)ˣ, ∃ (i : Fin n) (b : (w.adicCompletion F)ˣ),
        (((∏ᶠ σ : ↥(NumberField.PlaceDecomp.decomp E F w), σ • b : (w.adicCompletion F)ˣ) : (w.adicCompletion F)ˣ) :
            w.adicCompletion F) =
          IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F (⟨w, hw⟩ : v.Extension (𝓞 F))
            ((a * (c i)⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) := by sorry
