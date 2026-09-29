-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_whittakerLoc_eq_of_mem_gl3CyclicSubspace_of_isOpen
-- name    : LanglandsTunnell.CubicInduction.exists_isCubicInductionDataOn_whittakerLoc_eq_of_mem_gl3CyclicSubspace_of_isOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/6df5560b-e4e6-562a-a25c-0c685086935c
-- title:
--   Re-choosing one local Whittaker factor within its cyclic span
-- statement:
--   Fix a number field $K$, with $\mathcal O_K$ an integral $\mathcal O_{\mathbb Q}$-algebra, a continuous additive character $\psi$ of $\mathbb A_{\mathbb Q}$, a homomorphism $\mu$ from the idele group of $K$ to $\mathbb C^\times$, a set $D$ of adelic $2\times 2$ invertible matrices over $\mathbb Q$, a family $U$ of subgroups of that adelic $GL_2$ indexed by the ideals of $\mathcal O_{\mathbb Q}$, an element $\mathrm{gen}(v)$ of it for each finite place $v$, a set $S$ of finite places, and data $X$ consisting of a form on adelic $GL_3$ over $\mathbb Q$, a global Whittaker function, local Whittaker functions on each $GL_3(\mathbb Q_v)$, an archimedean Whittaker function, a central character and a dual Whittaker function. Assume $X$ satisfies `IsCubicInductionDataOn` relative to $K$, $\mu$, $\psi$, $S$ and the pins `productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)` (adelic Haar measure and Borel structure on $GL_2$, carrier $D$, full central subgroup, levels $U$, generators $\mathrm{gen}$, and adelic additive Haar measure conditioned on the adelic box): automorphy and central-character transformation of the form, an idele-class central character, cuspidality along both maximal parabolics, the $\psi$-Whittaker law and expansion, factorisation of the Whittaker function into the archimedean function times local factors over any finite set containing $S$, induced-sphericity and level-invariance outside $S$, local multiplicity one, moderate growth, $K$-finiteness, iota-moment and Whittaker half-plane conditions, and the dual analogues — summarised here. Assume further that $X.form$, $X.whittaker$ and $X.dualWhittaker$ are continuous and that the latter two are gauge-majorised in the sense of `IsGaugeMajorised3` (support inside a root-level region and, on it, decay $C/(\mathrm{rootSizeProd}^{\,t}(1+\mathrm{archRootSum})^N)$ for every $N$). Let $v\in S$ be such that $X.whittakerLoc\,v$ is invariant under right translation by some open subgroup of $GL_3(\mathbb Q_v)$, and let $W'$ lie in the $\mathbb C$-span of the right translates of $X.whittakerLoc\,v$. Then there exist data $Y$ satisfying the same `IsCubicInductionDataOn` conditions for the same $K,\mu,\psi,S$ and pins, with $Y.whittakerLoc\,v = W'$, with $Y.whittakerLoc\,u = X.whittakerLoc\,u$ for every $u\neq v$, with the same archimedean Whittaker function and central character as $X$, with $Y.form$, $Y.whittaker$, $Y.dualWhittaker$ continuous, and with $Y.whittaker$ and $Y.dualWhittaker$ gauge-majorised.
--
--   This is the local-modification step in the construction of automorphic data on $GL_3$ by cubic induction: one local Whittaker factor at a place of $S$ may be replaced by any element of the cyclic span of its right translates without disturbing the global laws, the remaining local factors, the archimedean factor, the central character, or the continuity and gauge-majorisation estimates. It is used to normalise the local factor at a bad place, as in [`LanglandsTunnell.CubicInduction.exists_isCubicInductionDataOn_whittakerLoc_one_eq_one_of_isBadPlace`](thm.html#LanglandsTunnell.CubicInduction.exists_isCubicInductionDataOn_whittakerLoc_one_eq_one_of_isBadPlace).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_whittakerLoc_eq_of_mem_gl3CyclicSubspace_of_isOpen.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.CubicInduction

theorem
  LanglandsTunnell.CubicInduction.exists_isCubicInductionDataOn_whittakerLoc_eq_of_mem_gl3CyclicSubspace_of_isOpen
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : Continuous ψ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (S : Set (HeightOneSpectrum (𝓞 ℚ))) (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ S X)
    (hcont : Continuous X.form) (hcontW : Continuous X.whittaker)
    (hcontW' : Continuous X.dualWhittaker)
    (hmaj : IsGaugeMajorised3 ℚ X.whittaker) (hmaj' : IsGaugeMajorised3 ℚ X.dualWhittaker)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∈ S)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, X.whittakerLoc v (g * k) = X.whittakerLoc v g)
    (W' : LocalGL3 v → ℂ) (hW' : W' ∈ gl3CyclicSubspace (X.whittakerLoc v)) :
    ∃ Y : CubicInductionData,
      IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ S Y ∧
        Y.whittakerLoc v = W' ∧ (∀ u, u ≠ v → Y.whittakerLoc u = X.whittakerLoc u) ∧
          Y.whittakerArch = X.whittakerArch ∧ Y.centralChar = X.centralChar ∧
            Continuous Y.form ∧ Continuous Y.whittaker ∧ Continuous Y.dualWhittaker ∧
              IsGaugeMajorised3 ℚ Y.whittaker ∧ IsGaugeMajorised3 ℚ Y.dualWhittaker := by sorry
