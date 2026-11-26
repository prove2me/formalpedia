-- Prove2me | Theorems.Thm_FriedCrossing_fried_counterexample_of_inputs
-- name    : FriedCrossing.fried_counterexample_of_inputs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:54:47.168836+00:00
-- url     : https://prove2.me/theorems/302b7243-9f34-4a7e-ba0a-ba63d21fc846
-- title:
--   Fried Crossing: fried counterexample of inputs
-- statement:
--   **Fried's identity fails at the crossing metric** — THE LEDGER. One binder per fact.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_counterexample_main.lean#L100-L193
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_counterexample_main.lean#L100-L193

import Definitions.Def_B1s_cluster_from_resolvent_9_11
import Definitions.Def_B1s_fried_counterexample_main
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology TwinRate FirstVariation Hadamard PureZeros Capstone OrderCount TorsionCore
  Derived Regularity Ledger Branch
set_option linter.unusedVariables false

theorem FriedCrossing.fried_counterexample_of_inputs
    {V₃ : Type*} [AddCommGroup V₃] [Module ℝ V₃]
    (M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (A : ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (sStar : ℝ → ℝ) (Bcc Bcψ Bψc Bψψ p : ℝ)
    -- [D] hstates: two linearly independent resonant states at s*(θ) in the degree-1 cluster at
    --     g_hyp — d₀f (from the degree-0 state f) and I·d₀f (I = rotation on E_u ⊕ E_s commutes
    --     with the flow, CDDP (3.7)); independence by the Liouville argument on S² (rederivation
    --     A2). The cluster's rank 2 is the TYPE Fin 2 [DGRS Prop 7.7 m₁(0) = 2b₁ at θ = 0 +
    --     bounded-twist rank constancy]. Together they GIVE M(θ,0) = s*·1 (`Derived.semisimple_of_states`,
    --     the former `hsemisimple`).
    (hstates : ∀ θ, ∃ v₁ v₂ : Fin 2 → ℝ, LinearIndependent ℝ ![v₁, v₂] ∧
      Matrix.mulVec (M θ 0) v₁ = sStar θ • v₁ ∧ Matrix.mulVec (M θ 0) v₂ = sStar θ • v₂)
    -- [U] INPUT (B), the whole of it: the entries of both cluster matrices are jointly C³ in
    --     (θ,τ). CDDP Lemma 4.3 gives continuity of the resolvent; the derivatives are resolvent
    --     perturbation on a flow-independent anisotropic space (target: Bonthonneau 1806.08125);
    --     the Cauchy-estimate alternative is vault input_b_cauchy_route_9_09 (PROPOSED).
    (hclusterC3 : ClusterC3 M A)
    -- [V] CDDP (4.22) + (4.38) + Lemmas 2.2/2.10, for ∂_τM(0,0) = `Derived.Mτ M 0 0`.
    (h422 : FirstVariation422 (Mτ M) Bcc Bcψ Bψc Bψψ p)
    -- [V] r₀ := Bcc·p/det B ≠ 0 is CDDP's non-degeneracy (1.3) for b in the open dense set O
    --     (Thm 1(2)); the sign is the orientation of τ.
    (hr₀ : 0 < Bcc * p / (Bcc * Bψψ - Bcψ * Bψc))
    -- [V] s*(θ) = −1 + √(1−μ₀(θ)): DGRS (7.6) as a meromorphic identity + BuOl Cor 5.1 (scalar
    --     Selberg zeros, cited via DGRS) + DFG Thm 2 cross-check; μ₀ by Kato–Rellich.
    (hdouble : DoublePoint sStar)
    -- [V]+[D] mirror (input A): the degree-2 cluster at g_hyp has spectrum {s*, s*, s*, −s*} —
    --     the locked pair at s* (DGRS Lemma 7.1) and the pure pair at ±s*: DGRS (7.6) k = 2
    --     factors Z_{S,σ₀}(λ) and Z_{S,σ₀}(λ+2) (dgrs 1876–1884) + BuOl zeros [V]; the −s* state
    --     identified as f'·ω_s (rederivation A2, rate-ratio memo §2.1) [D].
    (hmirror : ∀ θ z, (A θ 0).charpoly.eval z = (z - sStar θ) ^ 3 * (z + sStar θ))
    -- [V] pinning (input D) at ρ_triv: det M(0,τ) = 0 (the harmonic 1-form, b₁ = 1) and
    --     spec A(0,τ) = {0, 0, 0, twin} — 0 with multiplicity b₁ + 2 = 3 (CDDP Cor 4.1 via
    --     Thm 1(2)) and the lifted twin d₀u_nc (DGRS Lemma 7.1), whose value is tr M(0,τ).
    (hpinning : Pinned M A)
    -- [V] locked branches: every degree-1 cluster eigenvalue is a degree-2 cluster eigenvalue —
    --     d₀ commutes with L_X (DGRS Lemma 7.1) lifts the twin; ∧dα lifts the closed branch
    --     (f·dα = d₀²f/s_cl).
    (hlocked : ∀ θ τ z, (M θ τ).charpoly.eval z = 0 → (A θ τ).charpoly.eval z = 0) :
    let a : ℝ → ℝ → ℝ := fun θ τ => (Ndiv M (Mτ M) sStar θ τ).trace
    let b : ℝ → ℝ → ℝ := fun θ τ => (Ndiv M (Mτ M) sStar θ τ).det
    let a' : ℝ → ℝ → ℝ := aτ M
    let b' : ℝ → ℝ → ℝ := bτ M sStar
    let e₁ : ℝ → ℝ → ℝ := E₁f M A
    let e₂ : ℝ → ℝ → ℝ := E₂f M A
    let e₂τ : ℝ → ℝ → ℝ := pτ e₂
    -- the pure-zero branch: the root of z² − e₁z + e₂ nearest 0 (through 0 at a crossing, where 0
    -- is a simple root; `Branch.zBranch_at_simple_zero`). DEFINED — no binder.
    let z : ℝ → ℝ → ℝ := fun θ => zBranch (e₁ θ) (e₂ θ)
    let r₀ : ℝ := Bcc * p / (Bcc * Bψψ - Bcψ * Bψc)
    ∃ K₁ : ℝ, 0 < K₁ ∧ ∃ θ₀ δ : ℝ, 0 < θ₀ ∧ 0 < δ ∧ ∀ θ, θ ≠ 0 → |θ| < θ₀ →
      ∀ (ζ₀ F : ℝ → ℝ) (c : Fin 5 → ℕ) (τR : ℝ),
        -- [V] τ_R(χ_θ) ≠ 0: Reidemeister torsion of an acyclic character (Fried 1986 at g_hyp).
        ∀ (hτR : τR ≠ 0),
        -- [V] Chaubet–Dang (6.5) at λ = 0 along the family: ζ₀(τ) = ζ(0; g_τ) = F(τ)·z(τ)/s_nc(τ)
        --     off the crossing (`off`), the regular factor F continuous at the crossing (`cont`,
        --     input (B)), and ζ₀(σ) = F(σ) at the crossing where the cluster factor is λ/λ
        --     (`at_crossing`). z is the DEFINED pure-zero branch.
        ∀ (hfactor : ZetaFactorization ζ₀ F (twin sStar a b θ) (z θ) δ),
        -- [V] off the crossing Fried holds: ζ(0; g_τ) = τ_R — DGRS Thm 2 local constancy of
        --     ζ(0) in the vector field + Fried at g_hyp.
        ∀ (hfried_off : ∀ τ, |τ| < δ → twin sStar a b θ τ ≠ 0 → ζ₀ τ = τR),
        -- [V] the reduced resonant complex C₀¹ → C₀² → C₀³ at each crossing inside |τ| < δ is
        --     exact (Dang–Rivière Thm 2.1 / DGRS (7.1), rederivation A6), with C₀¹, C₀² the
        --     generalized 0-eigenspaces of the cluster matrices and C₀³ the abstract V₃.
        ∀ (hexact : ∀ τ₀, |τ₀| < δ → twin sStar a b θ τ₀ = 0 →
          ∃ (f : resZero₁ M θ τ₀ →ₗ[ℝ] resZero₂ A θ τ₀) (g : resZero₂ A θ τ₀ →ₗ[ℝ] V₃),
            Function.Injective f ∧ LinearMap.range f = LinearMap.ker g ∧ Function.Surjective g),
        -- [V] c₀ = c₄ = 0 for acyclic unitary ρ: DGRS Lemma 7.4 (+ ⋆).
        ∀ (hacyc : c 0 = 0 ∧ c 4 = 0),
        -- [V] c₃ = c₁: ⋆-duality, DGRS Lemma 7.2.
        ∀ (hdual : c 3 = c 1),
        -- [def] c_k = dim C₀^k, k = 1, 2, 3, at each crossing inside |τ| < δ (dimensions of the
        --     generalized 0-eigenspaces = algebraic multiplicities of 0, by Mathlib).
        ∀ (hdims : ∀ τ₀, |τ₀| < δ → twin sStar a b θ τ₀ = 0 →
          c 1 = Module.finrank ℝ (resZero₁ M θ τ₀) ∧ c 2 = Module.finrank ℝ (resZero₂ A θ τ₀) ∧
          c 3 = Module.finrank ℝ V₃),
        -- ══ CONCLUSION ═══════════════════════════════════════════════════════════════════════
        ∃ σ, 0 < σ ∧ σ ≤ 2 * |sStar θ| / r₀ ∧ σ < δ ∧ twin sStar a b θ σ = 0 ∧
          (∀ τ, |τ| < δ → twin sStar a b θ τ = 0 → τ = σ) ∧          -- unique crossing
          zetaOrder c = 0 ∧                                            -- ζ regular at 0
          HasDerivAt (z θ) (e₂τ θ σ / e₁ θ σ) σ ∧ 2 * r₀ < |e₂τ θ σ / e₁ θ σ| ∧   -- zero steeper
          |e₁ θ σ| ≤ K₁ * |θ| * σ ∧                                    -- than the pole
          ∃ α ratio : ℝ, α ≠ 0 ∧ dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ ≠ 0 ∧
            Tendsto (fun τ => twin sStar a b θ τ / z θ τ) (𝓝[≠] σ) (𝓝 ratio) ∧
            ratio = dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ / α ∧ ratio ≠ 1 ∧
            ζ₀ σ = τR * ratio ∧ ζ₀ σ ≠ τR ∧                            -- ζ(0;g_σ) ≠ τ_R
            refinedTorsion 1 (dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ /
              (α - dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ)) =
              -(α / dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ) := by sorry
