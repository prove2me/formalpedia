-- Prove2me | Theorems.Thm_FriedCrossing_Capstone_fried_fails_at_crossing_of_matrix_inputs
-- name    : FriedCrossing.Capstone.fried_fails_at_crossing_of_matrix_inputs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:51:47.216653+00:00
-- url     : https://prove2.me/theorems/22684179-9b09-4944-a6d8-3f5004d2677c
-- title:
--   Capstone: fried fails at crossing of matrix inputs
-- statement:
--   FRIED FAILS AT THE CROSSING — THE MATRICES AS PRIMITIVES. Compared with
--   `fried_fails_at_crossing_of_pure_zero_inputs`: the four regularity bundles are replaced by
--   [the former capstone `fried_fails_at_crossing_of_pure_zero_inputs` was removed 9/16 as superseded]
--   `ClusterC3` (joint C³ of the two cluster matrices); mirror and pinning are stated as spectra of the
--   degree-2 matrix; the locked branches enter as `hlocked` (degree-1 eigenvalues recur in degree 2);
--   `hexactZero` and `hgeneric` are DERIVED from exactness through the dictionary `hriesz`
--   (c_k = algebraic multiplicity of 0 in the degree-k cluster matrix). e₁, e₂, ∂_τM, a', b' are all
--   DEFINED from M and A; ⚡9/11: so is the pure-zero branch z = `Branch.zBranch` (root of Q nearest 0),
--   which removes the former `hzQ` and `hbranch`; and the ζ-side enters as the two facts it really is —
--   `ZetaFactorization` (CD (6.5) at λ = 0, with ζ₀(τ) = ζ(0; g_τ) and F its regular factor) and
--   `hfried_off` = "ζ₀ = τ_R off the crossing" (DGRS Thm 2 + Fried at g_hyp).
--   Conclusion: ζ₀(σ) ≠ τ_R.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L811-L957
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L811-L957

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Capstone
open TwinRate Hadamard FirstVariation Derived Spectral ClusterMatrix Ledger OrderCount TorsionCore
  Regularity Branch

theorem FriedCrossing.Capstone.fried_fails_at_crossing_of_matrix_inputs
    {V₃ : Type*} [AddCommGroup V₃] [Module ℝ V₃]
    (M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (A : ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (sStar : ℝ → ℝ) (Bcc Bcψ Bψc Bψψ p : ℝ)
    (hsemisimple : ∀ θ, M θ 0 = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hC3 : ClusterC3 M A)
    (hdet : Bcc * Bψψ - Bcψ * Bψc ≠ 0)
    (h422 : Bmat Bcc Bcψ Bψc Bψψ * Mτ M 0 0 = Pmat p)
    (hr₀ : 0 < Bcc * p / (Bcc * Bψψ - Bcψ * Bψc))
    (hsStar0 : sStar 0 = 0) (hsStarc : ContinuousAt sStar 0)
    (hsStarneg : ∀ θ, θ ≠ 0 → sStar θ < 0)
    (hmirror : ∀ θ z, (A θ 0).charpoly.eval z = (z - sStar θ) ^ 3 * (z + sStar θ))
    (hpinned : Pinned M A)
    (hlocked : ∀ θ τ z, (M θ τ).charpoly.eval z = 0 → (A θ τ).charpoly.eval z = 0) :
    let a : ℝ → ℝ → ℝ := fun θ τ => (Ndiv M (Mτ M) sStar θ τ).trace
    let b : ℝ → ℝ → ℝ := fun θ τ => (Ndiv M (Mτ M) sStar θ τ).det
    let a' : ℝ → ℝ → ℝ := aτ M
    let b' : ℝ → ℝ → ℝ := bτ M sStar
    let e₁ : ℝ → ℝ → ℝ := E₁f M A
    let e₂ : ℝ → ℝ → ℝ := E₂f M A
    let e₂τ : ℝ → ℝ → ℝ := pτ e₂
    let z : ℝ → ℝ → ℝ := fun θ => zBranch (e₁ θ) (e₂ θ)
    let r₀ : ℝ := Bcc * p / (Bcc * Bψψ - Bcψ * Bψc)
    ∃ K₁ : ℝ, 0 < K₁ ∧ ∃ θ₀ δ : ℝ, 0 < θ₀ ∧ 0 < δ ∧ ∀ θ, θ ≠ 0 → |θ| < θ₀ →
      ∀ (ζ₀ F : ℝ → ℝ) (c : Fin 5 → ℕ) (τR : ℝ),
        τR ≠ 0 →
        ZetaFactorization ζ₀ F (twin sStar a b θ) (z θ) δ →
        (∀ τ, |τ| < δ → twin sStar a b θ τ ≠ 0 → ζ₀ τ = τR) →
        (∀ τ₀, |τ₀| < δ → twin sStar a b θ τ₀ = 0 →
          ∃ (f : resZero₁ M θ τ₀ →ₗ[ℝ] resZero₂ A θ τ₀) (g : resZero₂ A θ τ₀ →ₗ[ℝ] V₃),
            Function.Injective f ∧ LinearMap.range f = LinearMap.ker g ∧ Function.Surjective g) →
        (c 0 = 0 ∧ c 4 = 0) → c 3 = c 1 →
        (∀ τ₀, |τ₀| < δ → twin sStar a b θ τ₀ = 0 →
          c 1 = Module.finrank ℝ (resZero₁ M θ τ₀) ∧ c 2 = Module.finrank ℝ (resZero₂ A θ τ₀) ∧
          c 3 = Module.finrank ℝ V₃) →
        ∃ σ, 0 < σ ∧ σ ≤ 2 * |sStar θ| / r₀ ∧ σ < δ ∧ twin sStar a b θ σ = 0 ∧
          (∀ τ, |τ| < δ → twin sStar a b θ τ = 0 → τ = σ) ∧
          zetaOrder c = 0 ∧
          HasDerivAt (z θ) (e₂τ θ σ / e₁ θ σ) σ ∧ 2 * r₀ < |e₂τ θ σ / e₁ θ σ| ∧
          |e₁ θ σ| ≤ K₁ * |θ| * σ ∧
          ∃ α ratio : ℝ, α ≠ 0 ∧ dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ ≠ 0 ∧
            Tendsto (fun τ => twin sStar a b θ τ / z θ τ) (𝓝[≠] σ) (𝓝 ratio) ∧
            ratio = dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ / α ∧ ratio ≠ 1 ∧
            ζ₀ σ = τR * ratio ∧ ζ₀ σ ≠ τR ∧
            refinedTorsion 1 (dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ /
              (α - dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ)) =
              -(α / dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ) := by sorry
