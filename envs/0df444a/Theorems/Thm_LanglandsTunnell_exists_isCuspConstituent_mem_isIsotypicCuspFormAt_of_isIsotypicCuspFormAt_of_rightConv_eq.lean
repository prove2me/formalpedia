-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_isCuspConstituent_mem_isIsotypicCuspFormAt_of_isIsotypicCuspFormAt_of_rightConv_eq
-- name    : LanglandsTunnell.exists_isCuspConstituent_mem_isIsotypicCuspFormAt_of_isIsotypicCuspFormAt_of_rightConv_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/3512b71d-a896-5686-aa50-c0ef73a917c4
-- title:
--   Isotypic cusp form replaced inside one cuspidal constituent
-- statement:
--   Work over $\mathbb{Q}$ with the pin data `productionPinsGeneral ℚ`. Let $\xi$ be a homomorphism from the central subgroup $Z$ of these pins to $\mathbb{C}^\times$, let $N$ be a non-zero ideal of $\mathcal{O}_{\mathbb{Q}}$, let $S$ be a finite set of height-one primes, let $\Phi$ be a complex Hecke eigensystem (a non-zero level ideal together with families $a_v,b_v$ of complex numbers indexed by primes), and let $\varphi\colon GL_2(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ be an isotypic cusp form for $(\xi,N,S,\Phi)$: a smooth cuspidal automorphic function for the pins with central character $\xi$, continuous, right invariant under the level group $U(N)$ of the pins, a Hecke coset eigenfunction for the generator at each $v\notin S$ with eigenvalue $\Phi.a\,v$, and satisfying $\varphi(\mathrm{diag}(\det g_v)\,g)=\Phi.b\,v\cdot\varphi(g)$ for $v\notin S$, where $g_v$ is the Hecke generator at $v$. Assume $\varphi\neq0$; that $\varphi$ is reproduced by right convolution $\int\varphi(gx)\alpha(x)\,dx$ against some factorizable test function $\alpha$ (a product of an archimedean and a finite-adelic test factor); and that at every real infinite place $w$ the function $\varphi$ satisfies `HasArchCharacterAt₀` for the weight character $n$-th power of `archWeightOneAt hw`, for some $n\in\mathbb{Z}$. Then there are a submodule $V$ of the complex-valued functions on $GL_2(\mathbb{A}_{\mathbb{Q}})$ which is a cusp subrepresentation for $(\text{pins},\xi)$, non-zero, and minimal in the sense that every cusp subrepresentation contained in it is $\bot$ or $V$, and a function $\varphi'\in V$ such that $\varphi'$ is again a non-zero isotypic cusp form for the same $(\xi,N,S,\Phi)$, is again reproduced by right convolution against some factorizable test function, and inherits each of the following archimedean conditions from $\varphi$, at every real place $w$: having weight character of index $n$; being archimedean-smooth with $\mathrm{Cas}\,\varphi=\lambda\varphi$ for the Casimir operator built from the directional derivatives $H,E,F^-$; satisfying $\varphi(g\cdot J)=e\,\varphi(g)$ for all $g$, where $J$ is the real reflection at $w$; and being annihilated by $H-i(E+F^-)$.
--
--   This is the passage from an arbitrary typed Hecke eigenvector in the cuspidal spectrum to one lying in a single cuspidal constituent, so that the archimedean analysis (weight, Casimir eigenvalue, reflection parity, lowering) can be carried out inside an irreducible piece; it rests on the discrete decomposition of the cuspidal spectrum with finite multiplicities. It is used in the Langlands–Tunnell part of the argument, in the construction of archimedean Casimir eigenvectors of minimal weight with non-vanishing Whittaker coefficient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_isCuspConstituent_mem_isIsotypicCuspFormAt_of_isIsotypicCuspFormAt_of_rightConv_eq.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem LanglandsTunnell.exists_isCuspConstituent_mem_isIsotypicCuspFormAt_of_isIsotypicCuspFormAt_of_rightConv_eq
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (Φ : HeckeEigensystem ℚ ℂ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Φ φ)
    (hne : φ ≠ 0)
    (hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ)
    (hwt : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ∃ n : ℤ, HasArchCharacterAt₀ ℚ w (archWeightCharAt hw n) φ) :
    ∃ (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) (φ' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ),
      CuspidalConstituent.IsCuspConstituent ℚ (productionPinsGeneral ℚ) ξ V ∧
      φ' ∈ V ∧
      IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Φ φ' ∧
      φ' ≠ 0 ∧
      (∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ' α = φ') ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (n : ℤ),
        HasArchCharacterAt₀ ℚ w (archWeightCharAt hw n) φ → HasArchCharacterAt₀ ℚ w (archWeightCharAt hw n) φ') ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (lam : ℂ),
        (IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = lam • φ) →
          (IsArchSmoothAt hw φ' ∧ archCasimirAt hw φ' = lam • φ')) ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (e : ℂ),
        (∀ g : AdelicGL2 (𝓞 ℚ) ℚ, φ (g * archRealGLAt hw UpperHalfPlane.J) = e * φ g) →
          ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, φ' (g * archRealGLAt hw UpperHalfPlane.J) = e * φ' g) ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
        archDerivAt hw ArchDir.H φ
            - Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ) = 0 →
          archDerivAt hw ArchDir.H φ'
            - Complex.I • (archDerivAt hw ArchDir.E φ' + archDerivAt hw ArchDir.Fm φ') = 0) := by sorry
