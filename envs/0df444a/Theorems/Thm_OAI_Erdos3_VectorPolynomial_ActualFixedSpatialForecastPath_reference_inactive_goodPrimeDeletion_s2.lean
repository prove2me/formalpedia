-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialForecastPath_reference_inactive_goodPrimeDeletion_s2
-- name    : OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.reference_inactive_goodPrimeDeletion_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T05:40:58.240072+00:00
-- url     : https://prove2.me/theorems/3a65f433-b0a4-4fee-8d98-210eebd44d43
-- title:
--   Deleting good large primes changes the inactive reference forecast of a fixed spatial forecast path by a factor 1 ± δ
-- statement:
--   **Setting.** Let $m$ be a natural number, $G$ a finite type, $I : \mathrm{Fin}\ m \to \mathrm{Type}$ a family of finite types, $n : \mathrm{Fin}\ m \to \mathbb{N}$, $B$ a family of finite types indexed by `LayerSamplerAxis I n`, $J$ a family of finite types indexed by $\mathrm{Fin}\ m$, $U_j$ a real subspace of $J_j \to \mathbb{R}$, $b_j$ a basis indexed by $\mathrm{Fin}\ (n\ j)$ of the orthogonal complement of `euclideanSubspace (U j)`, $R, \sigma : \mathrm{Fin}\ m \to \mathbb{R}$ with $R_j > 0$ and $\sigma_j > 0$ for all $j$, and $S$ a `LayerSamplerScale B U b R σ` (defined by OpenAI). Let $X$ be a finite type with decidable equality, $E_{\mathrm{out}}$ a family of finite types indexed by $\mathrm{Fin}\ m$, $D_{\mathrm{mod}}, L_{\mathrm{rank}}$ natural numbers, `spatial`, `kernel`, `block` families of embeddings of the types required by OpenAI's structure, $T_{\mathrm{sp}}$ a type, an equivalence $G \simeq X \oplus (X \oplus T_{\mathrm{sp}})$, real numbers $W_{\mathrm{sp}}, L_{\mathrm{sp}}, \tau, \delta_{\mathrm{slice}}, P, P_{\mathrm{bad}}, P_{\mathrm{pres}}$, and $N_{\mathrm{phys}} : X \to \mathbb{N}$. Let `path` be an `ActualFixedSpatialForecastPath B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres` with output types $E_{\mathrm{out}}$ (a structure defined by OpenAI recording a base point, noise, a coefficient sample with its readout, a finite set of primes `path.primes` with exponents `path.exponent` and prescribed depths `path.prescribed`, CRT origins, and bad-prime bounds). Write $M$ = `path.referenceModulus` $= \prod_{p \in \texttt{path.primes}} p^{\texttt{path.exponent}\ p}$ (a positive integer).
--
--   **Hypotheses.** Let $\Omega$ be a finite type and $Z$ a type. Suppose $0 < m$ and $|X| + \sum_{j} (|E_{\mathrm{out}}\ j| + n_j) \le D_{\mathrm{mod}}$. Let `inactive` be a `FiniteProbabilityWeights Ω` (a probability weight vector on $\Omega$, defined by OpenAI), `gridPoint` $: \Omega \to Z$, and `raw` $: \Omega \to (\texttt{PrincipalTupleIndex B (layerSamplerDegree I n)} \times \texttt{Option Empty}) \to \mathbb{Z}$. Let `cutoff` be a natural number with $0 <$ `cutoff` and $2/\texttt{cutoff} \le 1/2$, let $\delta \ge 0$ be real with $4/\texttt{cutoff} \le \delta$, let $V$ = `gridVolume` $\ge 0$ be real, let $z \in Z$, and let $\beta$ be a function from `Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis U b S.value))` (an output index type defined by OpenAI) to $\mathbb{Z}/M$.
--
--   **Conclusion.** Let
--   - `full` = `rationalInactiveForecast inactive (fun _ => path.referenceInputLaw) gridPoint (fun i => integerLongPolynomialOutput path.referencePolynomial (raw i) M) M V z β`, i.e. $V$ times the `inactive`-mean, restricted to the fiber `gridPoint` $= z$, of the density at $\beta$ of the image modulo $M$ of the reference polynomial `path.referencePolynomial` evaluated with inactive inputs `raw i` and long inputs drawn from the CRT input law `path.referenceInputLaw` (all defined by OpenAI);
--   - `truncated` = `path.retainedReferenceForecast inactive gridPoint raw cutoff V z β`, i.e. $V$ times the same fiber mean of the product, over the retained primes `path.referenceRetainedPrimes cutoff` (those primes of `path.primes` that have nonzero bad depth, or nonzero prescribed depth, or are at most `cutoff`), of the local densities `path.referenceLocalDensity (raw i) β p` (defined by OpenAI).
--
--   Then $(1 - \delta)\cdot \texttt{truncated} \le \texttt{full}$ and $\texttt{full} \le (1 + \delta)\cdot \texttt{truncated}$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.reference_inactive_goodPrimeDeletion_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.reference_inactive_goodPrimeDeletion` (in `lean/OAI/Combinatorics/Progressions/Lattices/ActualFixedSpatialGoodPrimeDeletion.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B252` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/ActualFixedSpatialGoodPrimeDeletion.lean (declaration OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.reference_inactive_goodPrimeDeletion)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B252

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

attribute [local instance] OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.retainedReferencePrimeNeZero
attribute [local instance] OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.retainedReferenceModulusNeZero
omit [Fintype Tsp] in

theorem reference_inactive_goodPrimeDeletion_s2 {Ω Z : Type*} [Fintype Ω]
    (hm : 0 < m)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod)
    (inactive : FiniteProbabilityWeights Ω) (gridPoint : Ω → Z)
    (raw : Ω → PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (cutoff : ℕ) (hcutoff : 0 < cutoff) (hsmall : 2 / (cutoff : ℝ) ≤ 1 / 2)
    {δ : ℝ} (hδ : 0 ≤ δ) (haccuracy : 4 / (cutoff : ℝ) ≤ δ)
    (gridVolume : ℝ) (hvolume : 0 ≤ gridVolume) (z : Z)
    (β : Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod path.referenceModulus) :
    let full := rationalInactiveForecast inactive (fun _ => path.referenceInputLaw) gridPoint
      (fun i => integerLongPolynomialOutput path.referencePolynomial (raw i) path.referenceModulus)
      path.referenceModulus gridVolume z β
    let truncated := path.retainedReferenceForecast inactive gridPoint raw cutoff gridVolume z β
    (1 - δ) * truncated ≤ full ∧ full ≤ (1 + δ) * truncated := by
  sorry

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end
