-- Prove2me | Theorems.Thm_FriedCrossing_fried_counterexample_of_resolvent_inputs
-- name    : FriedCrossing.fried_counterexample_of_resolvent_inputs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:08:44.33725+00:00
-- url     : https://prove2.me/theorems/6197063a-c795-4f36-9487-354aa3b84dee
-- title:
--   Fried Crossing: fried counterexample of resolvent inputs
-- statement:
--   **Fried's identity fails at the crossing metric — no uncited input.** The cluster matrices are
--   M := `Mreal F₁ J₁ D₁` (2×2, degree 1) and A := `Mreal F₂ J₂ D₂` (4×4, degree 2): real parts of the
--   frame matrices A(p)⁻¹B(p) built from contour integrals of matrix elements of the resolvent families.
--   Input (B) is replaced by the fields of `F₁`, `F₂` (CDDP Lemma 4.3 + generator smoothness, [V]) and
--   the frame nondegeneracy `hdet₁`, `hdet₂` ([def]: dual frame at (0,0), CP20 §6.2). Every other binder is
--   as in `fried_counterexample_of_inputs`.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_counterexample_main.lean#L205-L264
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_counterexample_main.lean#L205-L264

import Definitions.Def_B1s_cluster_from_resolvent_9_11
import Definitions.Def_B1s_fried_counterexample_main
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology TwinRate FirstVariation Hadamard PureZeros Capstone OrderCount TorsionCore
  Derived Regularity Ledger Branch
open Scale ClusterFrame
set_option linter.unusedVariables false

theorem FriedCrossing.fried_counterexample_of_resolvent_inputs
    {V₃ : Type*} [AddCommGroup V₃] [Module ℝ V₃]
    {S₁ S₂ : BanachScale.{0}}
    (F₁ : ResolventFamily S₁ Param) (J₁ : ComplexStructure S₁) (D₁ : FrameData S₁ 2)
    (F₂ : ResolventFamily S₂ Param) (J₂ : ComplexStructure S₂) (D₂ : FrameData S₂ 4)
    (sStar : ℝ → ℝ) (Bcc Bcψ Bψc Bψψ p : ℝ)
    -- [def] the frames are nondegenerate: det A(p) ≠ 0 (dual frame at (0,0), retracted parameters).
    (hdet₁ : ∀ q, (Amat F₁ J₁ D₁ q).det ≠ 0)
    (hdet₂ : ∀ q, (Amat F₂ J₂ D₂ q).det ≠ 0)
    -- [D] two independent states d₀f, I·d₀f at s*(θ) in the degree-1 cluster at g_hyp
    --     (rederivation A2); rank 2 = the type.
    (hstates : ∀ θ, ∃ v₁ v₂ : Fin 2 → ℝ, LinearIndependent ℝ ![v₁, v₂] ∧
      Matrix.mulVec (Mreal F₁ J₁ D₁ θ 0) v₁ = sStar θ • v₁ ∧
      Matrix.mulVec (Mreal F₁ J₁ D₁ θ 0) v₂ = sStar θ • v₂)
    (h422 : FirstVariation422 (Mτ (Mreal F₁ J₁ D₁)) Bcc Bcψ Bψc Bψψ p)
    (hr₀ : 0 < Bcc * p / (Bcc * Bψψ - Bcψ * Bψc))
    (hdouble : DoublePoint sStar)
    (hmirror : ∀ θ z, (Mreal F₂ J₂ D₂ θ 0).charpoly.eval z = (z - sStar θ) ^ 3 * (z + sStar θ))
    (hpinning : Pinned (Mreal F₁ J₁ D₁) (Mreal F₂ J₂ D₂))
    (hlocked : ∀ θ τ z, (Mreal F₁ J₁ D₁ θ τ).charpoly.eval z = 0 →
      (Mreal F₂ J₂ D₂ θ τ).charpoly.eval z = 0) :
    let M := Mreal F₁ J₁ D₁
    let A := Mreal F₂ J₂ D₂
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
        ∀ (hτR : τR ≠ 0),
        ∀ (hfactor : ZetaFactorization ζ₀ F (twin sStar a b θ) (z θ) δ),
        ∀ (hfried_off : ∀ τ, |τ| < δ → twin sStar a b θ τ ≠ 0 → ζ₀ τ = τR),
        ∀ (hexact : ∀ τ₀, |τ₀| < δ → twin sStar a b θ τ₀ = 0 →
          ∃ (f : resZero₁ M θ τ₀ →ₗ[ℝ] resZero₂ A θ τ₀) (g : resZero₂ A θ τ₀ →ₗ[ℝ] V₃),
            Function.Injective f ∧ LinearMap.range f = LinearMap.ker g ∧ Function.Surjective g),
        ∀ (hacyc : c 0 = 0 ∧ c 4 = 0),
        ∀ (hdual : c 3 = c 1),
        ∀ (hdims : ∀ τ₀, |τ₀| < δ → twin sStar a b θ τ₀ = 0 →
          c 1 = Module.finrank ℝ (resZero₁ M θ τ₀) ∧ c 2 = Module.finrank ℝ (resZero₂ A θ τ₀) ∧
          c 3 = Module.finrank ℝ V₃),
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
