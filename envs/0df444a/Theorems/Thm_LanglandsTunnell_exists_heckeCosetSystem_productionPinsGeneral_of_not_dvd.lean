-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_heckeCosetSystem_productionPinsGeneral_of_not_dvd
-- name    : LanglandsTunnell.exists_heckeCosetSystem_productionPinsGeneral_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/f94b6dec-da41-5371-901b-e2796d08dde7
-- title:
--   Hecke coset system at a place prime to the level
-- statement:
--   Let $F$ be a number field, $N$ an ideal of its ring of integers $\mathcal{O}_F$, and $v$ a point of the height-one spectrum of $\mathcal{O}_F$ whose prime ideal `v.asIdeal` does not divide $N$. Consider the carrier data `productionPinsGeneral F`, assembled from the Siegel set `classRepSiegelSet F (1/2) 1 (1/2) 2`, the level subgroups $N \mapsto$ `levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F`, the Hecke generators $v \mapsto$ `heckeGen (𝓞 F) F v` and the box `adelicBox F`; write $U =$ `(productionPinsGeneral F).U N` for its level subgroup at $N$ and $g =$ `(productionPinsGeneral F).gen v` for its generator at $v$, both inside $\mathrm{GL}_2$ of the adele ring of $F$, i.e. `AdelicGL2 (𝓞 F) F`. The assertion is that there is a family $\gamma : \mathrm{Fin}(\mathrm{N}(v)+1) \to \mathrm{GL}_2(\mathbb{A}_F)$, indexed by a set of cardinality $\mathrm{Ideal.absNorm}(v.\mathrm{asIdeal}) + 1$, which is a Hecke coset system for $(U, g)$: each $\gamma_i$ lies in the double coset $U \cdot \{g\} \cdot U$; every element $x$ of that double coset satisfies $xU = \gamma_i U$ for some $i$; and the map $i \mapsto \gamma_i U$ into $\mathrm{GL}_2(\mathbb{A}_F)/U$ is injective.
--
--   This is the spherical Hecke decomposition at a finite place prime to the level: the double coset $U\,\mathrm{diag}(\varpi_v,1)\,U$ splits into exactly $\mathrm{N}(v)+1$ left cosets modulo $U$, one for each point of $\mathbb{P}^1(\mathcal{O}_F/v)$, so that the Hecke operator $T_v$ has degree $\mathrm{N}(v)+1$. It supplies the coset systems used in the construction and comparison of automorphic forms and Hecke eigensystems over a number field in the Langlands–Tunnell part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_heckeCosetSystem_productionPinsGeneral_of_not_dvd.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LocalLanglands_HeckeCosetSystem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm

theorem LanglandsTunnell.exists_heckeCosetSystem_productionPinsGeneral_of_not_dvd
    (F : Type) [Field F] [NumberField F]
    (N : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ v.asIdeal ∣ N) :
    ∃ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 F) F,
      HeckeIntegralSeam.IsHeckeCosetSystem ((productionPinsGeneral F).U N)
        ((productionPinsGeneral F).gen v) reps := by sorry
