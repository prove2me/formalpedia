-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_isCuspConstituent_mem_isIsotypicCuspFormAt_of_isIsotypicCuspFormAt_of_rightConv_eq_whittakerCoefficient_add_smul_reflect_lower_ne_zero
-- name    : LanglandsTunnell.exists_isCuspConstituent_mem_isIsotypicCuspFormAt_of_isIsotypicCuspFormAt_of_rightConv_eq_whittakerCoefficient_add_smul_reflect_lower_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/fd82f9e7-712e-50be-91ef-a5fce28adbef
-- title:
--   Descent to a cuspidal constituent keeping a Whittaker non-vanishing
-- statement:
--   Work over $\mathbb{Q}$ with the carrier pins `productionPinsGeneral ℚ`. Given a character $\xi$ of the central subgroup of these pins into $\mathbb{C}^\times$, a nonzero ideal $N$ of $\mathbb{Z}$, a finite set $S$ of finite places, a Hecke eigensystem $\Phi$ (level data together with families $a,b$ of complex eigenvalues), and $\varphi : \mathrm{GL}_2(\mathbb{A}_\mathbb{Q}) \to \mathbb{C}$ satisfying `IsIsotypicCuspFormAt` for $(\xi,N,S,\Phi)$ — that is, $\varphi$ is a smooth cuspidal automorphic function for the pins and $\xi$, continuous, right invariant under the level subgroup $\mathrm{U}(N)$, a Hecke coset eigenfunction with eigenvalue $\Phi.a(v)$ for each $v \notin S$, and transforming by $\Phi$'s central value $b(v)$ under the central scalar $\det$ of the Hecke generator at such $v$ — assume $\varphi \neq 0$, that $\varphi$ is reproduced by right convolution against some factorizable test function $\alpha$ (an archimedean times a finite factor), that at every real place $w$ the function $\varphi$ satisfies `HasArchCharacterAt₀` for the character `archWeightCharAt hw n` (the $n$-th power of `archWeightOneAt`) for some integer $n$, and, for a chosen real place $w$, a scalar $\kappa$ and a point $g_1$, that the $\psi_\mathbb{Q}$-Whittaker coefficient at $\alpha = 1$ and $g_1$, namely $\int \Psi(u(x)g_1)\psi_\mathbb{Q}(-x)\,d\nu$, of $$\Psi = \varphi + \kappa\,\bigl(g \mapsto (D_H\varphi - i(D_E\varphi + D_{F^-}\varphi))(g\,J)\bigr)$$ is nonzero, where $D_H, D_E, D_{F^-}$ are the one-parameter derivatives `archDerivAt` at $w$ and $J$ is the image of `UpperHalfPlane.J` under `archRealGLAt hw`. The conclusion produces a submodule $V$ of $\mathbb{C}$-valued functions on $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$ and a function $\varphi'$ such that: $V$ is a cuspidal constituent for the pins and $\xi$ (a nonzero cuspidal subrepresentation all of whose cuspidal subrepresentations are $\bot$ or $V$); $\varphi' \in V$; $\varphi'$ again satisfies `IsIsotypicCuspFormAt` for the same $(\xi,N,S,\Phi)$; $\varphi' \neq 0$; the same Whittaker coefficient at $1$ and $g_1$ of $\varphi' + \kappa\,(g \mapsto (D_H\varphi' - i(D_E\varphi' + D_{F^-}\varphi'))(gJ))$ is nonzero; $\varphi'$ is reproduced by right convolution against some factorizable test function; and four archimedean conditions pass from $\varphi$ to $\varphi'$ at every real place $w$, namely the weight condition `HasArchCharacterAt₀` for `archWeightCharAt hw n` for each integer $n$, archimedean smoothness together with the Casimir eigenvalue equation $\Omega_w\varphi = \lambda\varphi$ for each $\lambda$, the eigenrelation $\varphi(gJ) = e\,\varphi(g)$ for each scalar $e$, and annihilation by the lowering combination $D_H - i(D_E + D_{F^-})$.
--
--   This isolates, inside the isotypic cusp space attached to a fixed character, level, exceptional set and Hecke eigensystem, a single irreducible cuspidal constituent containing a nonzero form with the same Hecke and archimedean behaviour, while additionally retaining the non-vanishing of a Whittaker functional of a fixed first-order archimedean combination — the functional used to detect the archimedean sign in the weight-one situation. It is used in [`LanglandsTunnell.exists_agreesAwayFromFinite_twist_archCasimir_eigenvector_weightOne_whittakerCoefficient_torus_eq_archW_mem_isCuspConstituent_whittaker_diagOne_ne_zero_of_whittakerCoefficient_fibre_eq_archW_of_ne_of_ne`](thm.html#LanglandsTunnell.exists_agreesAwayFromFinite_twist_archCasimir_eigenvector_weightOne_whittakerCoefficient_torus_eq_archW_mem_isCuspConstituent_whittaker_diagOne_ne_zero_of_whittakerCoefficient_fibre_eq_archW_of_ne_of_ne), on the route to the Langlands–Tunnell input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_isCuspConstituent_mem_isIsotypicCuspFormAt_of_isIsotypicCuspFormAt_of_rightConv_eq_whittakerCoefficient_add_smul_reflect_lower_ne_zero.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem LanglandsTunnell.exists_isCuspConstituent_mem_isIsotypicCuspFormAt_of_isIsotypicCuspFormAt_of_rightConv_eq_whittakerCoefficient_add_smul_reflect_lower_ne_zero
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (Φ : HeckeEigensystem ℚ ℂ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Φ φ)
    (hne : φ ≠ 0)
    (hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ)
    (hwt : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ∃ n : ℤ, HasArchCharacterAt₀ ℚ w (archWeightCharAt hw n) φ)

    (w : InfinitePlace ℚ) (hw : w.IsReal) (κ : ℂ) (g₁ : AdelicGL2 (𝓞 ℚ) ℚ)
    (hdev : whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ
        (φ + κ • (fun g : AdelicGL2 (𝓞 ℚ) ℚ =>
          (archDerivAt hw ArchDir.H φ - Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ))
            (g * archRealGLAt hw UpperHalfPlane.J))) 1 g₁ ≠ 0) :
    ∃ (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) (φ' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ),
      CuspidalConstituent.IsCuspConstituent ℚ (productionPinsGeneral ℚ) ξ V ∧
      φ' ∈ V ∧
      IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Φ φ' ∧
      φ' ≠ 0 ∧

      whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ
        (φ' + κ • (fun g : AdelicGL2 (𝓞 ℚ) ℚ =>
          (archDerivAt hw ArchDir.H φ' - Complex.I • (archDerivAt hw ArchDir.E φ' + archDerivAt hw ArchDir.Fm φ'))
            (g * archRealGLAt hw UpperHalfPlane.J))) 1 g₁ ≠ 0 ∧
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
