-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialSlicedForecastPath_scaledRetainedRecoveredG_lift_lipschitz_s2
-- name    : OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.scaledRetainedRecoveredG_lift_lipschitz_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T06:40:28.076084+00:00
-- url     : https://prove2.me/theorems/866eb8f8-5c5d-418e-b28c-29a2aca90cc9
-- title:
--   The scaled retained recovered kernel is Lipschitz in the lift variable
-- statement:
--   Fix the data of OpenAI's actual fixed-spatial forecast setting: a natural number $m$; a finite type $G$; finite types $I_j$ ($j \in \mathrm{Fin}\,m$) and $n : \mathrm{Fin}\,m \to \mathbb N$; finite types $B_a$ for $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \le \mathbb R^{J_j}$ and bases $b_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`; reals $R_j, \sigma_j$, a `LayerSamplerScale` $S$ for $(B, U, b, R, \sigma)$ over $G$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities), and proofs $hR$, $h\sigma$ that $R_j > 0$ and $\sigma_j > 0$ for all $j$; a finite type $X$ with decidable equality; finite types $E_j$ (`Eout`); natural numbers $D_{\mathrm{mod}}$ and $L$; embeddings $\mathrm{spatial} : \mathrm{Fin}\,L \hookrightarrow G$, $\mathrm{kernel}_j : \mathrm{Fin}\,L \times \mathrm{Fin}(j+1) \hookrightarrow G$, and $\mathrm{block}_{j,a} : \mathrm{Fin}\,L \hookrightarrow B_{\langle j, a\rangle}$ for every axis $a$ of layer $j$ that is not short (`AllocatedDegreeActiveAxis short j`, where $\mathrm{short}$ is the predicate `allocatedShortAxis U b S.value`); a finite type $T$ and an equivalence $G \simeq X \oplus (X \oplus T)$; reals $W_{\mathrm{sp}}, L_{\mathrm{sp}}$; $N : X \to \mathbb N$ (`physicalN`); and reals $\tau, \delta_{\mathrm{slice}}, P, P_{\mathrm{bad}}, P_{\mathrm{pres}}$. Let `slice` be an `ActualFixedSpatialSlicedForecastPath` over these data (a structure bundling an `ActualFixedSpatialForecastPath` `slice.path` over the same data with a step $> 0$, kernel lengths and starts, principal lengths, steps and starts, and identities tying them to the path). Let $A$ be a finite type and $\mathrm{selected} : A \to \Sigma_j\, \mathrm{Fin}(n_j)$; $hB$ a proof that $|B_a| \ge 4$ for every axis $a$ that is not short; $o_j$ orthonormal bases of `euclideanSubspace (U j)` indexed by $I_j$; $bW_j$ $\mathbb Z$-bases, indexed by $E_j$, of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`; $hb$ the statement that the $\mathbb Z$-span of $b_j$ is `projectedIntegerLattice (euclideanSubspace (U j))`; $d$ a natural number and $e : \mathrm{Fin}\,d \simeq \Sigma_j J_j$; `cutoff` a natural number and $\kappa \in \mathbb R_{\ge 0}$. Write $\mathcal M =$ `slice.path.referenceRetainedCRTModulus cutoff` (a product of prime powers defined by OpenAI).
--
--   Let $C : \mathrm{Fin}\,m \to \mathbb R_{\ge 0}$ with $\|\phi_j(z)\| \le C_j \|z\|$ for all $j, z$, where $\phi_j$ is `normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)`; let $K \in \mathbb R_{\ge 0}$ with $R_j^{-1} \le K$ for all $j$; let $D_{\mathrm{lip}}, R_{\mathrm{cap}} \in \mathbb R_{\ge 0}$ such that `slice.density hB` (a real function defined by OpenAI) is $D_{\mathrm{lip}}$-Lipschitz and $|$`slice.retainedRecoveredRationalFactor selected bW hb e cutoff ρ β`$| \le R_{\mathrm{cap}}$ for all $\rho : X \to \mathbb Z/\mathcal M$ and $\beta : \mathrm{Fin}\,d \to \mathbb Z$ (a real defined by OpenAI). Then for every $v : X \to \mathbb R$, every $\rho : X \to \mathbb Z/\mathcal M$ and every $\beta : \mathrm{Fin}\,d \to \mathbb Z$, the function
--   $$y \in \mathbb R^d \mapsto \mathrm{slice.scaledRetainedRecoveredG}(\mathrm{selected}, hB, o, bW, hb, e, \mathrm{cutoff}, \kappa, v, \rho, \beta, y)$$
--   ($\kappa$ times OpenAI's real function `retainedRecoveredG`) is Lipschitz with constant $\kappa \cdot R_{\mathrm{cap}} \cdot D_{\mathrm{lip}} \cdot K \sum_j C_j |J_j|$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.scaledRetainedRecoveredG_lift_lipschitz_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.scaledRetainedRecoveredG_lift_lipschitz` (in `lean/OAI/Combinatorics/Progressions/Linear/ActualFixedSpatialScaledRetainedKernelBounds.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B303` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Linear/ActualFixedSpatialScaledRetainedKernelBounds.lean (declaration OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.scaledRetainedRecoveredG_lift_lipschitz)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B303

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable {d : ℕ} (e : Fin d ≃ Σ j, J j)

variable (cutoff : ℕ) (κ : ℝ≥0)

theorem scaledRetainedRecoveredG_lift_lipschitz_s2
    (C : Fin m → ℝ≥0)
    (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    {Dlip Rcap : ℝ≥0} (hdensity : LipschitzWith Dlip (slice.density hB))
    (hcap : ∀ residue β,
      |slice.retainedRecoveredRationalFactor selected bW hb e cutoff residue β| ≤ Rcap)
    (v : X → ℝ) (residue : X → ZMod (slice.path.referenceRetainedCRTModulus cutoff))
    (β : Fin d → ℤ) :
    LipschitzWith (κ * (Rcap * (Dlip * (K * ∑ j, C j * Fintype.card (J j)))))
      (slice.scaledRetainedRecoveredG selected hB o bW hb e cutoff κ v residue β) := by
  sorry

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end
