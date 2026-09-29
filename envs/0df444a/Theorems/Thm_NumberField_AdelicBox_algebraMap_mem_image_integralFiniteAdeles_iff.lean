-- Prove2me | Theorems.Thm_NumberField_AdelicBox_algebraMap_mem_image_integralFiniteAdeles_iff
-- name    : NumberField.AdelicBox.algebraMap_mem_image_integralFiniteAdeles_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/9a1bff24-2463-56ea-9c62-20b504152625
-- title:
--   Principal finite adeles in the coset k + dwidehat𝒪_F
-- statement:
--   Let $F$ be a number field, with ring of integers $\mathcal O_F =$ `𝓞 F` and finite adele ring $\mathbb A_F^f =$ `FiniteAdeleRing (𝓞 F) F`. Let $d \in \mathcal O_F$ be nonzero and let $k, \xi \in F$. Write $\iota$ for the structure map `algebraMap F (FiniteAdeleRing (𝓞 F) F)`, and let $\widehat{\mathcal O}_F =$ `integralFiniteAdeles (𝓞 F) F` be the set of those finite adeles $x$ whose component $x_v$ lies in the valuation ring `v.adicCompletionIntegers F` of the completion at $v$ for every $v$ in the height-one spectrum of $\mathcal O_F$. The assertion is the equivalence of the following two statements: first, that $\iota(\xi)$ belongs to the image of $\widehat{\mathcal O}_F$ under the map $z \mapsto \iota(k) + \iota(d)\,z$ on $\mathbb A_F^f$, that is, $\iota(\xi) \in \iota(k) + \iota(d)\,\widehat{\mathcal O}_F$; and second, that there exists $a \in \mathcal O_F$ with $\xi = k + d\,a$ as elements of $F$.
--
--   This is the local–global statement $F \cap \widehat{\mathcal O}_F = \mathcal O_F$ in the form needed for cosets: the principal finite adeles lying in the compact open coset $k + d\,\widehat{\mathcal O}_F$ are exactly those coming from the lattice $k + d\,\mathcal O_F \subset F$. It is used in the adelic Fourier-analytic computations of the project, where sums over $F$ of pure tensors against indicator functions of such cosets are reindexed by $k + d\,\mathcal O_F$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicBox_algebraMap_mem_image_integralFiniteAdeles_iff.lean

import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicBox IsDedekindDomain
open scoped nonZeroDivisors

theorem NumberField.AdelicBox.algebraMap_mem_image_integralFiniteAdeles_iff
    (F : Type) [Field F] [NumberField F] (d : 𝓞 F) (hd : d ≠ 0) (k ξ : F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ ∈
        (fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F
      ↔ ∃ a : 𝓞 F, ξ = k + (d : F) * (a : F) := by sorry
