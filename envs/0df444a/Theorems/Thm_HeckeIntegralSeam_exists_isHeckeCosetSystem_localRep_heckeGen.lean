-- Prove2me | Theorems.Thm_HeckeIntegralSeam_exists_isHeckeCosetSystem_localRep_heckeGen
-- name    : HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/5229d7b7-99c7-5b8e-938b-ec4a42dc956e
-- title:
--   Explicit coset system for the Hecke double coset at v
-- statement:
--   Let $F$ be a number field and let $v$ be a nonzero prime of $\mathcal{O}_F$, with completion $F_v$ and valuation ring $\mathcal{O}_v =$ `v.adicCompletionIntegers F`. The assertion is that there exist $\varpi \in \mathcal{O}_v$ and a proof $h$ that its image in $F_v$ is nonzero such that: (i) $\mathrm{Valued.v}(\varpi) = \exp(-1)$, i.e. $\varpi$ is a uniformizer; (ii) the element $\mathrm{diag}(\varpi,1) \in \mathrm{GL}_2(F_v)$ (the unit `diagPi ϖ h`, with inverse $\mathrm{diag}(\varpi^{-1},1)$), placed at the component $v$ with all other finite components $1$ by `localEmbed` and with archimedean component $1$ by `finEmbed`, equals the Hecke generator `heckeGen (𝓞 F) F v` in $\mathrm{GL}_2(\mathbb{A}_F)$; and (iii) there is a map $\sigma \colon \mathcal{O}_F/\mathfrak{p}_v \to \mathcal{O}_F$ with $\sigma(c) \bmod \mathfrak{p}_v = c$ for all $c$, such that for every ideal $M$ of $\mathcal{O}_F$ with $\mathfrak{p}_v \nmid M$ the family indexed by $\mathrm{Option}(\mathcal{O}_F/\mathfrak{p}_v)$ whose value at `none` is the image in $\mathrm{GL}_2(\mathbb{A}_F)$ of $w\,\mathrm{diag}(\varpi,1)\,w$ ($w$ the Weyl element `weylInt`) and whose value at `some c` is the image of $u(\sigma(c))\,\mathrm{diag}(\varpi,1)$ (with $u$ the integral unipotent `unipotentInt`, $\sigma(c)$ read in $\mathcal{O}_v$) satisfies `IsHeckeCosetSystem` for the subgroup $U =$ `levelOne (𝓞 F) F M` $\sqcap$ `finiteAdelicGL2Subgroup F` (the latter the kernel of the archimedean projection `glArch`) and the element `heckeGen (𝓞 F) F v`: each representative lies in $U\,\mathrm{heckeGen}\,U$, every element of that double coset has the same class in $\mathrm{GL}_2(\mathbb{A}_F)/U$ as some representative, and the induced map to $\mathrm{GL}_2(\mathbb{A}_F)/U$ is injective.
--
--   This is the classical decomposition of the Hecke double coset at a finite place $v$ into $q_v+1$ cosets — one upper-triangular representative for each residue class modulo $\mathfrak{p}_v$ and one further representative conjugated by the Weyl element — made explicit in terms of a uniformizer and a section of the residue map, with the identification of the local diagonal element with the global Hecke generator recorded alongside. It underlies the expression of the Hecke operator at $v$ as a finite sum of translates, and is used throughout the adelic treatment of automorphic forms (isotypic and cuspidal conditions at $v$, Rankin–Selberg integrals, local realisations).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeIntegralSeam_exists_isHeckeCosetSystem_localRep_heckeGen.lean

import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm LocalGL2 AdelicDock NumberField.AdelicLevel

theorem HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ ϖ : v.adicCompletionIntegers F,
      ∃ hϖ0 : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ ≠ 0,
        Valued.v (ϖ : v.adicCompletion F) = WithZero.exp (-1 : ℤ) ∧
        finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)) = heckeGen (𝓞 F) F v ∧
        ∃ sec : 𝓞 F ⧸ v.asIdeal → 𝓞 F,
          (∀ c : 𝓞 F ⧸ v.asIdeal, Ideal.Quotient.mk v.asIdeal (sec c) = c) ∧
          ∀ M : Ideal (𝓞 F), ¬ v.asIdeal ∣ M →
            HeckeIntegralSeam.IsHeckeCosetSystem
              (levelOne (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F) (heckeGen (𝓞 F) F v)
              (fun i : Option (𝓞 F ⧸ v.asIdeal) =>
                finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v
                  (i.elim (localRepInf ϖ hϖ0)
                    (fun c => localRepSome ϖ hϖ0
                      (algebraMap (𝓞 F) (v.adicCompletionIntegers F) (sec c)))))) := by sorry
