-- Prove2me | Theorems.Thm_GEGIAMP_Relative_proposition_8_2
-- name    : GEGIAMP.Relative.proposition_8_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:54:36.756792+00:00
-- url     : https://prove2.me/theorems/1ba86b2f-29cd-4f33-b170-a060414524be
-- title:
--   Proposition 8.2 — exact state evolution at finite dimension
-- statement:
--   For fixed deterministic $\omega_k>0$ and $d\le N$: conditional on the side variables, the entries of $Z$ from (6.13), including the final proof-only output, are independent standard Gaussians, with the same conditional law for every value of the side variables; so $Z$ is independent of them and the pairs (row $i$ of $Z$, side variables of coordinate $i$) are independent copies over $i$. After marginalizing, the reconstructed $G_{j,i}$ are independent $N(0,h)$, the paths $(Y_{j,i},\widehat M_{j,i}-\sqrt\Delta)_{j=0}^K$ are independent copies of $(Y_j,M^\omega_j)_{j=0}^K$ of (6.7)–(6.8), and the coordinates of $f$ are independent copies of $M^\omega_K$. No independence of $Z$ from $A$ or the full $J$ is asserted.
--
--   Differences from the source:
--   - reading: Φ_γ is the solution of the Parisi PDE (2.3); m = Φₓ, a = Φₓₓ → Φ is `value` of the published SKFullSupport bundle (the stochastic-control formula (5.2)); m = `gradient`, a = `curvature` (Lean `deriv`), aₓ, aₓₓ further `deriv`s; reason: the paper identifies Φ with (5.2) on p. 15 (citing [AC17, Cor. 2]); Proposition 5.1 gives the spatial derivatives below time one
--   - encoding: "we fix a minimizing γ" (p. 7) and Assumption 2.1 for the Parisi diffusion (2.5) → hypothesis `Standing W γ`: IsMinimizer W γ and E[m(t,X_t)²] = t (0 ≤ t < 1) for every X with IsDiffusion W γ X (the integral form of (2.5)); reason: standing hypotheses of §§3, 7–9, written as binders
--   - reading: the grid and quadrature of the algorithm at its internal accuracy → every positive constants κ, every 0 < ε ≤ 1, Γ^q of (6.6); reason: the proposition is stated for the algorithm’s construction at any accuracy
--   - encoding: conditional law of Z given the side variables, "the same for every value" → for every fixed value η of the side variables, the law of Z under GOE(N) ⊗ law(J) is the standard Gaussian product on Fin N × Fin d; reason: the regular conditional law of an independent product is this section law
--   - encoding: "Z is independent of these variables, and the pairs … are independent copies over i" → the joint law of (row i of Z, side variables of coordinate i)_{i<N} is the N-fold product of N(0, I_d) ⊗ N(0, I); reason: one product-law identity states both independences and the marginals
--   - encoding: queries, groups and Z’s columns 1, …, d → 0-based indices; column B of Z is the proof-only output z_d; reason: Lean convention
-- source:
--   Herman, Chakrabarti, Kim, Ozgul (2026), A Fully Polynomial Approximation Algorithm for the Sherrington–Kirkpatrick Model, arXiv:2611.05446v1 (version not printed; held file SHA-256 ea6508afbf5e8771a5353c9c9ce9df52a08608793fb812fc9ba947719fd5658e), Proposition 8.2, p. 40

import Mathlib
import Definitions.Def_GEGIAMP_Relative_Algorithm

open MeasureTheory ProbabilityTheory OAI.ZeroTemperatureSK
open scoped ENNReal NNReal Topology

namespace GEGIAMP.Relative

/-- **Proposition 8.2** (exact state evolution; Herman, Chakrabarti, Kim, Ozgul (2026), arXiv:2611.05446v1, SHA-256 ea6508af…5658e, p. 40). For fixed deterministic
normalization factors `ω_k > 0` and `d ≤ N`: conditional on the side variables, the entries of
`Z = [z_1 | ⋯ | z_d]` from (6.13), including the final proof-only output, are independent
standard Gaussians, with the same conditional law for every value of the side variables;
hence `Z` is independent of them and the pairs (row `i` of `Z`, side variables of coordinate
`i`) are independent copies over `i`. After marginalizing, the reconstructed `G_{j,i}` are
independent `N(0, h)`, the paths `(Y_{j,i}, M̂_{j,i} − √Δ)_{j=0}^K`, `1 ≤ i ≤ N`, are
independent copies of `(Y_j, M^ω_j)_{j=0}^K` of (6.7)–(6.8), and the coordinates of `f` are
independent copies of `M^ω_K`. (No independence of `Z` from `A` or `J` is asserted.) -/
theorem proposition_8_2 {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (γ : OrderParameter) (hγ : Standing W γ) (κ : AlgConsts) (hκ : κ.Pos) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (N : ℕ) (hdN : (params κ ε).d ≤ N) (ω : ℕ → ℝ)
    (hω : ∀ k, 0 < ω k) :
    let P := params κ ε
    let mo := mF W γ
    let ao := aF W γ
    let Γc := Gq (gam γ) κ ε
    -- conditional on every value of the side variables, Z is standard Gaussian
    (∀ η : SideIdx P.B N P.mf → ℝ,
      Measure.map (fun AJ : (Fin N → Fin N → ℝ) × (Fin P.d → Fin P.d → ℝ) =>
          fun p : Fin N × Fin P.d => Zext mo ao P Γc ω AJ.1 (Jfun AJ.2) (sideFun η) p.1 p.2)
        ((RandMatDisc.goe N).prod (jLaw N P.d)) =
      Measure.pi fun _ : Fin N × Fin P.d => gaussianReal 0 1) ∧
    -- (row i of Z, side variables of coordinate i) are i.i.d. over i, Z ⊥ side variables
    Measure.map (fun x : MatSpace N P => fun i : Fin N =>
        ((fun s : Fin P.d => Zext mo ao P Γc ω x.1 (Jfun x.2.1) (sideFun x.2.2) i s),
         (fun q : Fin P.B × Fin (P.mf - 1) => x.2.2 (q.1, i, q.2))))
      (matLaw N P) =
    Measure.pi (fun _ : Fin N =>
      (Measure.pi fun _ : Fin P.d => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin P.B × Fin (P.mf - 1) => gaussianReal 0 1)) ∧
    -- the reconstructed increments are i.i.d. N(0, h)
    Measure.map (fun x : MatSpace N P => fun (i : Fin N) (j : Fin P.K) =>
        incr mo ao P Γc ω x.1 (Jfun x.2.1) (sideFun x.2.2) i j) (matLaw N P) =
      Measure.pi (fun _ : Fin N => gaussLaw P.K P.h) ∧
    -- the coordinate paths are independent copies of the scalar recursion
    Measure.map (fun x : MatSpace N P => fun (i : Fin N) (j : Fin (P.K + 1)) =>
        pathAt mo ao P Γc ω x.1 (Jfun x.2.1) (sideFun x.2.2) i j) (matLaw N P) =
      Measure.pi (fun _ : Fin N => Measure.map (fun g : Fin P.K → ℝ => fun j : Fin (P.K + 1) =>
        (Ys mo P.h Γc g j, Ms mo ao P.h Γc ω g j)) (gaussLaw P.K P.h)) ∧
    -- the coordinates of f are independent copies of M^ω_K
    Measure.map (fun x : MatSpace N P => fvec mo ao P Γc ω x.1 (Jfun x.2.1) (sideFun x.2.2))
        (matLaw N P) =
      Measure.pi (fun _ : Fin N =>
        Measure.map (fun g : Fin P.K → ℝ => Ms mo ao P.h Γc ω g P.K) (gaussLaw P.K P.h)) := by sorry

end GEGIAMP.Relative
