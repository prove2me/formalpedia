-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialForecastPath_localReference_uncharged_density
-- name    : OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.localReference_uncharged_density
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-16T01:22:06.710069+00:00
-- url     : https://prove2.me/theorems/66b1e8fa-cae6-4554-b6d8-6395d5d1d27b
-- title:
--   At an uncharged prime the local reference output density is within 2/p^2 of 1
-- statement:
--   Fix the data of OpenAI's actual fixed-spatial forecast setting: a natural number $m$; a finite type $G$; finite types $I_j$ ($j \in \mathrm{Fin}\,m$) and $n : \mathrm{Fin}\,m \to \mathbb N$; finite types $B_a$ for $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \le \mathbb R^{J_j}$ and bases $b_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`; reals $R_j, \sigma_j$, a `LayerSamplerScale` $S$ for $(B, U, b, R, \sigma)$ over $G$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities), and proofs $hR$, $h\sigma$ that $R_j > 0$ and $\sigma_j > 0$ for all $j$; a finite type $X$ with decidable equality; finite types $E_j$ (`Eout`); natural numbers $D_{\mathrm{mod}}$ and $L$; embeddings $\mathrm{spatial} : \mathrm{Fin}\,L \hookrightarrow G$, $\mathrm{kernel}_j : \mathrm{Fin}\,L \times \mathrm{Fin}(j+1) \hookrightarrow G$, and $\mathrm{block}_{j,a} : \mathrm{Fin}\,L \hookrightarrow B_{\langle j, a\rangle}$ for every axis $a$ of layer $j$ that is not short (`AllocatedDegreeActiveAxis short j`, where $\mathrm{short}$ is the predicate `allocatedShortAxis U b S.value`, true exactly of the axes $\langle j, \mathrm{inr}\ i\rangle$ with `basisAxisScale (b j) i` $\le S.\mathrm{value}^{j+1}$); a finite type $T$ and an equivalence $G \simeq X \oplus (X \oplus T)$; reals $W_{\mathrm{sp}}, L_{\mathrm{sp}}$; $N : X \to \mathbb N$ (`physicalN`); and reals $\tau, \delta_{\mathrm{slice}}, P, P_{\mathrm{bad}}, P_{\mathrm{pres}}$. Let `path` be an `ActualFixedSpatialForecastPath` over these data (a structure bundling a base point, a noise vector, sample arrays, an integer read-off, centers, a finite set `path.primes` of primes, functions `path.exponent` and `path.prescribed` from $\mathbb N$ to $\mathbb N$, origins `path.origin p` in $(\mathbb Z/p^{\mathrm{exponent}(p)})^{V}$ with $V =$ `LayerSamplerLongVariables short G B`, and further data with bounds).
--
--   Assume $m > 0$ and $|X| + \sum_j (|E_j| + n_j) \le D_{\mathrm{mod}}$. Let $\mathrm{raw}$ be an integer function on `PrincipalTupleIndex B (layerSamplerDegree I n)` $\times\ \mathrm{Option}\ \mathrm{Empty}$, let $p \in$ `path.primes` with `path.referenceBadDepth p` $= 0$ (a natural number, the `allocatedCongruenceBadDepth` of the path's data at $p$) and `path.prescribed p` $= 0$, and let $z$ be a function from $\Sigma_j$ `AllocatedCongruenceRankOutput X E short j` to $\mathbb Z/p^{e}$ with $e =$ `path.exponent p`. Put
--   $$\mathrm{density} = \mathrm{rationalOutputDensity}\bigl(\mathrm{uniform},\ Y,\ p^{e},\ z\bigr),$$
--   the number $|(\mathbb Z/p^e)^{\Sigma_j \mathrm{AllocatedCongruenceRankOutput}}|$ times the probability that the output $Y(x)$ reduced mod $p^e$ equals $z$, for $x$ uniform on $V \to \mathbb Z/p^e$, where $Y$ is `localPrimePowerIntegerPolynomialOutput p e (path.prescribed p) (path.localReferencePolynomial raw) (path.origin p)`: the integer output that evaluates the integer polynomials `path.localReferencePolynomial raw` (OpenAI's `allocatedCongruenceIntegerPolynomial` of the path's base, noise and read-off, with the frozen raw values) at the point $v \mapsto$ (the representative in $[0, p^e)$ of $\mathrm{origin}(v) + p^{\mathrm{prescribed}(p)} x(v)$, here with $p^{\mathrm{prescribed}(p)} = 1$). Then $|\mathrm{density} - 1| \le 2/p^2$ and $\mathrm{density} \le 1 + 2/p^2$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.localReference_uncharged_density` in `lean/OAI/Combinatorics/Progressions/Probability/ActualFixedSpatialUnchargedDensity.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B1331` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Probability/ActualFixedSpatialUnchargedDensity.lean#L116

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1331

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

omit [Fintype Tsp] in
theorem localReference_uncharged_density
    (hm : 0 < m)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod)
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (p : path.primes) (hbad : path.referenceBadDepth p.val = 0)
    (hpres : path.prescribed p.val = 0)
    (z : Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod (p.val ^ path.exponent p.val)) :
    letI := path.primeNeZero
    let density := rationalOutputDensity
      (FiniteProbabilityWeights.uniform
        (LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B →
          ZMod (p.val ^ path.exponent p.val)))
      (localPrimePowerIntegerPolynomialOutput p.val (path.exponent p.val) (path.prescribed p.val)
        (path.localReferencePolynomial raw) (path.origin p))
      (p.val ^ path.exponent p.val) z
    |density - 1| ≤ 2 / (p.val : ℝ) ^ 2 ∧ density ≤ 1 + 2 / (p.val : ℝ) ^ 2 := by
  sorry

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial
end
end OAI
