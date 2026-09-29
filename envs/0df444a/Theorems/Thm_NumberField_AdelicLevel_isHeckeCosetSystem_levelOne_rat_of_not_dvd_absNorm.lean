-- Prove2me | Theorems.Thm_NumberField_AdelicLevel_isHeckeCosetSystem_levelOne_rat_of_not_dvd_absNorm
-- name    : NumberField.AdelicLevel.isHeckeCosetSystem_levelOne_rat_of_not_dvd_absNorm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/cdea62cc-8eee-59ee-b98f-a64a79c82836
-- title:
--   Explicit left-coset representatives for the Hecke double coset at p over ℚ
-- statement:
--   Let $L$ be an ideal of $\mathcal{O}_{\mathbb{Q}}$, let $p$ be a prime number with $p \nmid \operatorname{absNorm} L$, let $v$ be a point of the height-one spectrum of $\mathcal{O}_{\mathbb{Q}}$ with $p \in v$, and let $\varpi$ be a unit of the completion $\mathbb{Q}_v$ whose underlying element is the image of $p \in \mathbb{Q}$ under the structure map $\mathbb{Q} \to \mathbb{Q}_v$. Put $U = \mathtt{levelOne}(L) \sqcap \mathtt{finiteAdelicGL2Subgroup}$, the subgroup of $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ consisting of those elements whose finite part (image under `glFin`) lies in the level-$L$ subgroup `finiteLevelOne` of $\mathrm{GL}_2$ of the finite adeles and which lie in the kernel of `glArch`, and let $g = \mathtt{heckeGen}(v)$ be the image under the homomorphism `diagOne` of the adelic unit that equals the chosen uniformiser unit at $v$, is $1$ at all other finite places and has trivial archimedean component. The assertion is that the family indexed by $i \in \mathrm{Fin}(p+1)$, given for $i < p$ by the product of the adele-valued matrix with trivial archimedean component whose finite part is the diagonal image of $\begin{pmatrix}1 & -i\\ 0 & 1\end{pmatrix} \in \mathrm{GL}_2(\mathbb{Q})$ with $\mathtt{heckeGenAt}(v)(\varpi)$, and for $i = p$ by the product of the central scalar matrix attached to the adelic unit that is $\varpi$ at $v$ and $1$ elsewhere with $\mathtt{heckeGenAt}(v)(\varpi)^{-1}$, is a Hecke coset system for $(U, g)$: every member lies in the double coset $U \cdot \{g\} \cdot U$, every element of that double coset is congruent modulo $U$ on the right to some member, and the induced map from $\mathrm{Fin}(p+1)$ to $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})/U$ is injective.
--
--   This is the adelic form of the classical decomposition of the Hecke double coset at a prime $p$ not dividing the level into $p+1$ left cosets, with unipotent representatives taken to be images of rational matrices so that a left $\mathrm{GL}_2(\mathbb{Q})$-invariant function may be evaluated on them. It is used in the identification of the adelic Hecke operator at $p$ with the classical $T_p$ acting on cusp forms of level $\Gamma_1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicLevel_isHeckeCosetSystem_levelOne_rat_of_not_dvd_absNorm.lean

import Mathlib
import Definitions.Def_AutomorphicForm_ProductionPinsCompact
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LocalLanglands_HeckeCosetSystem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.SiegelCoordinates
  IsDedekindDomain

theorem NumberField.AdelicLevel.isHeckeCosetSystem_levelOne_rat_of_not_dvd_absNorm
    (L : Ideal (𝓞 ℚ)) (p : ℕ) (hp : p.Prime) (hpL : ¬ p ∣ Ideal.absNorm L)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (p : 𝓞 ℚ) ∈ v.asIdeal)
    (ϖ : (v.adicCompletion ℚ)ˣ) (hϖ : (ϖ : v.adicCompletion ℚ) = algebraMap ℚ _ (p : ℚ)) :
    HeckeIntegralSeam.IsHeckeCosetSystem
      (levelOne (𝓞 ℚ) ℚ L ⊓ finiteAdelicGL2Subgroup ℚ) (heckeGen (𝓞 ℚ) ℚ v)
      (fun i : Fin (p + 1) =>
        if (i : ℕ) < p then
          AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
              (upperUnit (1 : ℚ) (-((i : ℕ) : ℚ)) 1 one_ne_zero one_ne_zero)))
            * heckeGenAt (𝓞 ℚ) ℚ v ϖ
        else
          centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v ϖ))
            * (heckeGenAt (𝓞 ℚ) ℚ v ϖ)⁻¹) := by sorry
