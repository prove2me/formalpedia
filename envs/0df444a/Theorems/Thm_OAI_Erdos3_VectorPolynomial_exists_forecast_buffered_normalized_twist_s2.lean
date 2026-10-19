-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_forecast_buffered_normalized_twist_s2
-- name    : OAI.Erdos3.VectorPolynomial.exists_forecast_buffered_normalized_twist_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T05:03:04.847742+00:00
-- url     : https://prove2.me/theorems/291d8740-7763-46c8-8a0a-8289a93e25b8
-- title:
--   A masked buffered covered site factor is twice a normalized polynomial twist with explicit Lipschitz constant
-- statement:
--   **Setting.** Let $m$ be a natural number, $G$ a finite type, $I : \mathrm{Fin}\ m \to \mathrm{Type}$ a family of finite types, $n : \mathrm{Fin}\ m \to \mathbb{N}$, $B$ a family of finite types indexed by `LayerSamplerAxis I n`, $J$ a family of finite types indexed by $\mathrm{Fin}\ m$, $U_j$ a real subspace of $J_j \to \mathbb{R}$, $b_j$ a basis indexed by $\mathrm{Fin}\ (n\ j)$ of the orthogonal complement of `euclideanSubspace (U j)` whose $\mathbb{Z}$-span is `projectedIntegerLattice (euclideanSubspace (U j))` (hypothesis $hb$), $R, \sigma : \mathrm{Fin}\ m \to \mathbb{R}$, $S$ a `LayerSamplerScale B U b R σ` (defined by OpenAI), $o_j$ an orthonormal basis of `euclideanSubspace (U j)` indexed by $I\ j$, $E$ a family of finite types indexed by $\mathrm{Fin}\ m$, and $bW_j$ a $\mathbb{Z}$-basis indexed by $E\ j$ of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`. Let $d$ be a nonzero natural number, $r \in \mathbb{R}_{\ge 0}$ with $r > 0$, $\mathrm{period}$ a nonzero natural number, and $X$ a finite type.
--
--   **Hypotheses.** Suppose $\mathrm{period}$ divides $d$ and $R_j > 0$ for all $j$. Let $C : \mathrm{Fin}\ m \to \mathbb{R}$ with $C_j \ge 0$, $\lVert \phi_j^{-1}(v) \rVert \le C_j \lVert v \rVert$ for all $j, v$, where $\phi_j$ = `normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)`, and $C_j\,\bigl((|I\ j| + 1)(2 r R_j)\bigr) \le 1/4$ for all $j$. Let $C_{\mathrm{fwd}} : \mathrm{Fin}\ m \to \mathbb{R}_{\ge 0}$ with $\lVert \phi_j(v) \rVert \le C_{\mathrm{fwd}, j} \lVert v \rVert$ for all $j, v$. Let $K \in \mathbb{R}_{\ge 0}$ with $R_j^{-1} \le K$ for all $j$. Let $\mathrm{mask} : (X \to \mathbb{Z}/\mathrm{period}) \to \mathbb{C}$ with $\lVert \mathrm{mask}(a) \rVert \le 1$ for all $a$. Let $F$ assign to each residue datum $a \in \prod_j (\mathrm{Fin}\ (n\ j) \oplus E\ j \to \mathbb{Z}/\mathrm{period})$ a function $F(a) : (X \to \mathbb{R}) \times (\texttt{LayerSamplerAxis I n} \to \mathbb{R}) \to \mathbb{C}$, and let $L \in \mathbb{R}_{\ge 0}$ with each $F(a)$ $L$-Lipschitz and $\lVert F(a)(z) \rVert \le 1$ for all $a, z$.
--
--   **Conclusion.** Put
--   - $L_{\mathrm{coord}} = K \sum_j C_{\mathrm{fwd}, j}\,|J_j|$,
--   - $L_{\mathrm{cut}} = \bigl(|\texttt{LayerSamplerAxis I n}|\cdot$`normalizedSiteCutoffBound`$/(2r)\bigr)\cdot L_{\mathrm{coord}}$, where `normalizedSiteCutoffBound` $\ge 1$ is a fixed constant chosen by OpenAI,
--   - $L_g = \max\bigl((L\cdot\max(1, L_{\mathrm{coord}}))\cdot\max(1, \mathrm{period}),\ 4\,\mathrm{period}\bigr)$,
--   - $L_{\mathrm{out}} = L_{\mathrm{cut}}\cdot\mathrm{period} + L_g$.
--
--   Then there is a `NormalizedPolynomialTwist X (Σ j, J j) period period L_out` (a structure defined by OpenAI consisting of a modulus, a cover, a mask of norm at most $1$ on residues modulo the modulus, and a smooth function of norm at most $1$ which is $L_{\mathrm{out}}$-Lipschitz; its modulus and cover are bounded by the given caps, here $\mathrm{period}$) called `twist`, with `twist.modulus` $= \mathrm{period}$ and `twist.cover` $= \mathrm{period}$, such that for all $N : X \to \mathbb{N}$, all real vector polynomials $p_j$ on $X$ with values in $J_j \to \mathbb{R}$ whose coefficients all lie in $U_j$ (hypothesis $hp$), and all $u : X \to \mathbb{Z}$,
--   $$\mathrm{mask}(u \bmod \mathrm{period})\cdot \texttt{forecastBufferedCoveredSiteFactor B U b S o hb bW d r hr period F}\ \bigl(i \mapsto u_i / N_i\bigr)\ \bigl(\texttt{physicalSingleSiteValue U d p hp}\ (i \mapsto u_i)\bigr) = 2\cdot \texttt{twist.eval}\ N\ p\ u.$$
--   Here `physicalSingleSiteValue U d p hp w` is the point of `EuclideanJetLayers U (fun _ => Unit)` obtained from the values $p_j(w)$ scaled by $1/d$ and reduced modulo the lattice; `forecastBufferedCoveredSiteFactor` is a complex function defined by OpenAI (a chart density built from a buffered site cutoff and $F$); and `twist.eval N p u` $= \texttt{twist.mask}(u \bmod \texttt{twist.modulus})\cdot \texttt{twist.smooth}\bigl(i \mapsto u_i/N_i,\ \texttt{physicalGridFactorInput twist.cover}\ p\ u\bigr)$ (with division by $N_i = 0$ giving $0$, as usual in Lean).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_forecast_buffered_normalized_twist_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.exists_forecast_buffered_normalized_twist` (in `lean/OAI/Combinatorics/Progressions/Sampling/ActualForecastModelPrecision.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B236` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/ActualForecastModelPrecision.lean (declaration OAI.Erdos3.VectorPolynomial.exists_forecast_buffered_normalized_twist)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B236

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r) (period : ℕ) [NeZero period]
variable {X : Type*} [Fintype X]

theorem exists_forecast_buffered_normalized_twist_s2
    (hdiv : period ∣ d)
    (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (mask : (X → ZMod period) → ℂ) (hmask : ∀ a, ‖mask a‖ ≤ 1)
    (F : (∀ j, Fin (n j) ⊕ E j → ZMod period) → (X → ℝ) × (LayerSamplerAxis I n → ℝ) → ℂ)
    {L : ℝ≥0} (hf : ∀ a, LipschitzWith L (F a)) (hf1 : ∀ a z, ‖F a z‖ ≤ 1) :
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Lcut := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord
    let Lg := max ((L * max 1 Lcoord) * max 1 (period : ℝ≥0)) (4 * period)
    let Lout := Lcut * period + Lg
    ∃ twist : NormalizedPolynomialTwist X (Σ j, J j) period period Lout,
      twist.modulus = period ∧ twist.cover = period ∧
      ∀ (N : X → ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
        (hp : ∀ j e, coefficients (p j) e ∈ U j) (u : X → ℤ),
        mask (fun i => (u i : ZMod period)) *
          forecastBufferedCoveredSiteFactor B U b S o hb bW d r hr period F
            (fun i => (u i : ℝ) / N i)
            (BooleanCubeKernel.physicalSingleSiteValue U d p hp (fun i => (u i : ℝ))) =
          2 * twist.eval N p u := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
