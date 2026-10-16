-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialSlicedForecastPath_targetAt_mean_mul_bufferedScalarScore_eq_fin
-- name    : OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.targetAt_mean_mul_bufferedScalarScore_eq_fin
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-16T01:32:53.907592+00:00
-- url     : https://prove2.me/theorems/ac102b5d-0a5a-4afd-a654-1c82f618fe47
-- title:
--   The target-weighted buffered score average as a sum over integer lifts
-- statement:
--   Fix the data of OpenAI's actual fixed-spatial forecast setting: a natural number $m$; a finite type $G$; finite types $I_j$ ($j \in \mathrm{Fin}\,m$) and $n : \mathrm{Fin}\,m \to \mathbb N$; finite types $B_a$ for $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \le \mathbb R^{J_j}$ and bases $b_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`; reals $R_j, \sigma_j$, a `LayerSamplerScale` $S$ for $(B, U, b, R, \sigma)$ over $G$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities), and proofs $hR$, $h\sigma$ that $R_j > 0$ and $\sigma_j > 0$ for all $j$; a finite type $X$ with decidable equality; finite types $E_j$ (`Eout`); natural numbers $D_{\mathrm{mod}}$ and $L$; embeddings $\mathrm{spatial} : \mathrm{Fin}\,L \hookrightarrow G$, $\mathrm{kernel}_j : \mathrm{Fin}\,L \times \mathrm{Fin}(j+1) \hookrightarrow G$, and $\mathrm{block}_{j,a} : \mathrm{Fin}\,L \hookrightarrow B_{\langle j, a\rangle}$ for every axis $a$ of layer $j$ that is not short (`AllocatedDegreeActiveAxis short j`, where $\mathrm{short}$ is the predicate `allocatedShortAxis U b S.value`); a finite type $T$ and an equivalence $G \simeq X \oplus (X \oplus T)$; reals $W_{\mathrm{sp}}, L_{\mathrm{sp}}$; $N : X \to \mathbb N$ (`physicalN`); and reals $\tau, \delta_{\mathrm{slice}}, P, P_{\mathrm{bad}}, P_{\mathrm{pres}}$. Let `slice` be an `ActualFixedSpatialSlicedForecastPath` over these data (a structure bundling an `ActualFixedSpatialForecastPath` `slice.path` over the same data with a step $> 0$, kernel lengths and starts, principal lengths, steps and starts, and identities tying them to the path). Let $A$ be a finite type and $\mathrm{selected} : A \to \Sigma_j\, \mathrm{Fin}(n_j)$; $hB$ a proof that $|B_a| \ge 4$ for every axis $a$ that is not short; $o_j$ orthonormal bases of `euclideanSubspace (U j)` indexed by $I_j$; $bW_j$ $\mathbb Z$-bases, indexed by $E_j$, of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`; $hb$ the statement that the $\mathbb Z$-span of $b_j$ is `projectedIntegerLattice (euclideanSubspace (U j))`; $d$ a natural number and $e : \mathrm{Fin}\,d \simeq \Sigma_j J_j$.
--
--   Let $\mathrm{poly}_j$ be vector polynomials on $X$ with values in $\mathbb R^{J_j}$ whose coefficients lie in $U_j$ (proof $hm$); $\kappa$ real; $\chi$ a `PatchKernel d` (a function $\mathbb R^d \to [0,1]$ supported where all $|x_i| \le 1/4$, Lipschitz); $T' : (X \to \mathbb Z) \to (\mathrm{Fin}\,d \to \mathbb Z) \to \mathbb R$; $f : (X \to \mathbb Z) \to \mathbb R$; and $\lambda$ real. Let $y =$ `fullTaggedBufferedCoordinates e poly c` with $c_j$ the vector of `slice.path.center j` (so $y(x)_i = \mathrm{poly}_{(e i).1}(x)_{(e i).2} - c_{e(i)}$), and $Q =$ `slice.path.referenceModulus`. Then
--   $$\mathop{\mathbb E}_{u \in \mathrm{integerBox\ physicalN}} \mathrm{Re}\bigl(\mathrm{slice.targetAt}(\mathrm{selected}, hB, o, bW, hb, \mathrm{poly}, hm, \kappa, u)\bigr)\cdot \mathrm{bufferedScalarScore}(\chi, y, T', f, \lambda, u)$$
--   equals the average over $u \in \prod_i \{0, \dots, N_i - 1\}$ of
--   $$(f(u) - \lambda) \sum_{\beta : \mathrm{Fin}\,d \to \mathbb Z} \chi\bigl(y(u) - \beta\bigr) \cdot \kappa\, \mathrm{slice.recoveredG}\bigl(\mathrm{selected}, hB, o, bW, hb, e, (u_i/N_i)_i, (u_i \bmod Q)_i, \beta, y(u) - \beta\bigr) \cdot T'(u, \beta)$$
--   (the sum is a `tsum`). Here `targetAt` is a complex number defined by OpenAI ($\kappa$ times a `forecastLawDensityPhysicalTarget` built from the slice's data), `bufferedScalarScore χ y T' f λ u` $= (f(u) - \lambda)\,\chi(y(u) - [y(u)])\, T'(u, [y(u)])$ with $[\cdot]$ the coordinatewise nearest-integer lift, and `recoveredG` is a real function defined by OpenAI.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.targetAt_mean_mul_bufferedScalarScore_eq_fin` in `lean/OAI/Combinatorics/Progressions/Sampling/ActualFixedSpatialBufferedScore.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B076`, `OAIErdos3B1344` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/ActualFixedSpatialBufferedScore.lean#L103

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B076
import Definitions.Def_OAIErdos3B1344

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

theorem targetAt_mean_mul_bufferedScalarScore_eq_fin
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j q, coefficients (poly j) q ∈ U j)
    (κ : ℝ) (χ : PatchKernel d)
    (T : (X → ℤ) → (Fin d → ℤ) → ℝ) (f : (X → ℤ) → ℝ) (lam : ℝ) :
    let coords := fullTaggedBufferedCoordinates e poly (fun j => (slice.path.center j).val)
    (𝔼 u : ↥(integerBox physicalN),
      (slice.targetAt selected hB o bW hb poly hm κ u.val).re *
        bufferedScalarScore χ coords T f lam u.val) =
      (𝔼 u : (∀ i, Fin (physicalN i)),
        (f (fun i => ((u i).val : ℤ)) - lam) * ∑' β : Fin d → ℤ,
        χ.value (fun i => coords (fun j => ((u j).val : ℤ)) i - (β i : ℝ)) *
          (κ * slice.recoveredG selected hB o bW hb e
            (fun i => ((u i).val : ℝ) / physicalN i)
            (fun i => ((u i).val : ZMod slice.path.referenceModulus)) β
            (fun i => coords (fun j => ((u j).val : ℤ)) i - (β i : ℝ))) *
          T (fun i => ((u i).val : ℤ)) β) := by
  sorry

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial
end
end OAI
