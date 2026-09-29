-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_exists_fin_forall_exists_finprod_smul_eq_mul_of_isMulCommutative_decomp
-- name    : NumberField.PlaceDecomp.exists_fin_forall_exists_finprod_smul_eq_mul_of_isMulCommutative_decomp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/a53c2b71-8f99-5987-9fe1-9dc16a372ed2
-- title:
--   Local norm index bound for abelian decomposition group
-- statement:
--   Let $E$ and $F$ be number fields with $F$ an $E$-algebra and $F/E$ Galois, let $v$ be a height-one prime of $\mathcal{O}_E$ and $w$ a height-one prime of $\mathcal{O}_F$ lying over it, in the sense that `w.under (𝓞 E) = v`, and assume that the group [`NumberField.PlaceDecomp.decomp E F w`](def/NumberField_PlaceDecompositionAction.html#L82) — the decomposition subgroup of $F \simeq_{\mathrm{alg}[E]} F$ attached to the valuation subring of the $w$-adic valuation of $F$ — is commutative. The assertion is that there exist a natural number $n$ and a family $c : \mathrm{Fin}\,n \to (E_v)^\times$ of units of the $v$-adic completion $E_v$ of $E$ such that $n$ is at most the cardinality of that decomposition group, and such that for every unit $a \in (E_v)^\times$ there are an index $i$ and a unit $b \in (F_w)^\times$ of the $w$-adic completion of $F$ with $$\prod_{\sigma \in \mathrm{decomp}(E,F,w)} \sigma \cdot b \;=\; \iota\bigl(a\,c_i^{-1}\bigr),$$ the product being the finite product of the translates of $b$ under the action of the decomposition group on $(F_w)^\times$, the equality being taken in $F_w$ after coercion from units, and $\iota$ being the semialgebra map [`IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom`](def/DedekindDomain_Completion_BaseChange.html#L425) from $E_v$ to $F_w$ associated with the extension $\langle w, hw\rangle$ of $v$. Thus the norms from $(F_w)^\times$ cover $(E_v)^\times$ up to the finite list $c_1,\dots,c_n$, with $n \le |\mathrm{decomp}(E,F,w)|$.
--
--   This is the elementary inequality $[E_v^\times : N_{F_w/E_v} F_w^\times] \le |D_w|$ for a local layer whose decomposition group is abelian, stated with an explicit finite system of coset representatives so that no norm subgroup or index need be named. It feeds the analysis of the local component of the idelic Artin map in [`M4aHerbrand.idelicArtinMap_single_eq_one_iff_exists_finprod_smul_eq`](thm.html#M4aHerbrand.idelicArtinMap_single_eq_one_iff_exists_finprod_smul_eq), and is obtained from the cyclic case together with a tower argument over the decomposition field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_exists_fin_forall_exists_finprod_smul_eq_mul_of_isMulCommutative_decomp.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_DedekindDomain_Completion_BaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxSynthPendingDepth 3
open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin
open scoped IsMulCommutative NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.exists_fin_forall_exists_finprod_smul_eq_mul_of_isMulCommutative_decomp
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 F)) (hw : w.under (𝓞 E) = v)
    [IsMulCommutative ↥(NumberField.PlaceDecomp.decomp E F w)] :
    ∃ (n : ℕ) (c : Fin n → (v.adicCompletion E)ˣ), n ≤ Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) ∧
      ∀ a : (v.adicCompletion E)ˣ, ∃ (i : Fin n) (b : (w.adicCompletion F)ˣ),
        (((∏ᶠ σ : ↥(NumberField.PlaceDecomp.decomp E F w), σ • b : (w.adicCompletion F)ˣ) : (w.adicCompletion F)ˣ) :
            w.adicCompletion F) =
          IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F (⟨w, hw⟩ : v.Extension (𝓞 F))
            ((a * (c i)⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) := by sorry
