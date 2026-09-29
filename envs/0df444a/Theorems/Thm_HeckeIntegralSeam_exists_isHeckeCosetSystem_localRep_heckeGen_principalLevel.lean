-- Prove2me | Theorems.Thm_HeckeIntegralSeam_exists_isHeckeCosetSystem_localRep_heckeGen_principalLevel
-- name    : HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen_principalLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/91b38ce5-dc49-51f7-8c14-35194c5c609b
-- title:
--   Explicit qᵥ+1 Hecke coset representatives at a finite place
-- statement:
--   Let $F$ be a number field and $v$ a nonzero prime of $\mathcal{O}_F$, with completion $F_v$ and valuation ring $\mathcal{O}_v$. The assertion is that there is an element $\varpi \in \mathcal{O}_v$ whose image in $F_v$ is nonzero (the nonvanishing proof being part of the data, since it enters the construction of the matrices below) such that: (i) the valuation of $\varpi$ in $F_v$ equals $\exp(-1)$, so $\varpi$ is a uniformizer; (ii) the element of $\mathrm{GL}_2(\mathbb{A}_F)$ obtained from $\mathrm{diag}(\varpi,1) \in \mathrm{GL}_2(F_v)$ by `localEmbed` (insert at the place $v$, all other finite components $1$) followed by `finEmbed` (archimedean component $1$) is exactly `heckeGen` at $v$, the Hecke generator built from the chosen uniformizer unit at $v$; and (iii) there is a set-theoretic section $\sigma$ of $\mathcal{O}_F \to \mathcal{O}_F/\mathfrak{p}_v$ such that for every ideal $M$ of $\mathcal{O}_F$ not divisible by $\mathfrak{p}_v$ the family indexed by $\mathrm{Option}(\mathcal{O}_F/\mathfrak{p}_v)$ whose value at $\mathrm{none}$ is the image of $w\,\mathrm{diag}(\varpi,1)\,w$ ($w$ the integral Weyl element) and at $\mathrm{some}\ c$ the image of $u(\sigma(c))\,\mathrm{diag}(\varpi,1)$, all transported by `localEmbed` then `finEmbed`, satisfies `IsHeckeCosetSystem` for the group $U = \mathrm{principalLevel}(M) \cap \ker(\mathrm{glArch})$ and the element `heckeGen` at $v$: every member lies in the double coset $U\,T_v\,U$, every element of $U\,T_v\,U$ lies in the same coset modulo $U$ as some member, and distinct indices give distinct cosets.
--
--   This is the classical decomposition of the local Hecke double coset at $v$ into $q_v+1$ cosets — one upper triangular representative for each residue class and one further representative with the uniformizer in the lower right corner — underlying the expression of $T(\mathfrak{p}_v)$ as a sum of $q_v+1$ translates, here stated adelically for the principal level $M$ prime to $v$ and with the representatives made explicit in terms of a uniformizer and a section of the residue map. It is used in the estimate [`AutomorphicForm.exists_setLIntegral_sub_sum_translate_sq_lt_of_agreesAwayFromFinite_of_coversModCentre_ample_principal`](thm.html#AutomorphicForm.exists_setLIntegral_sub_sum_translate_sq_lt_of_agreesAwayFromFinite_of_coversModCentre_ample_principal) for integrals of translates of automorphic functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeIntegralSeam_exists_isHeckeCosetSystem_localRep_heckeGen_principalLevel.lean

import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm LocalGL2 AdelicDock NumberField.AdelicLevel

theorem HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen_principalLevel
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ ϖ : v.adicCompletionIntegers F,
      ∃ hϖ0 : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ ≠ 0,
        Valued.v (ϖ : v.adicCompletion F) = WithZero.exp (-1 : ℤ) ∧
        finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)) = heckeGen (𝓞 F) F v ∧
        ∃ sec : 𝓞 F ⧸ v.asIdeal → 𝓞 F,
          (∀ c : 𝓞 F ⧸ v.asIdeal, Ideal.Quotient.mk v.asIdeal (sec c) = c) ∧
          ∀ M : Ideal (𝓞 F), ¬ v.asIdeal ∣ M →
            HeckeIntegralSeam.IsHeckeCosetSystem
              (principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F) (heckeGen (𝓞 F) F v)
              (fun i : Option (𝓞 F ⧸ v.asIdeal) =>
                finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v
                  (i.elim (localRepInf ϖ hϖ0)
                    (fun c => localRepSome ϖ hϖ0
                      (algebraMap (𝓞 F) (v.adicCompletionIntegers F) (sec c)))))) := by sorry
