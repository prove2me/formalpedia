-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_forecastDensityBufferedPhysicalAtom_s2
-- name    : OAI.Erdos3.VectorPolynomial.exists_forecastDensityBufferedPhysicalAtom_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:49:49.461985+00:00
-- url     : https://prove2.me/theorems/b2e4589d-05c9-48f4-a7d0-10e6997e515a
-- title:
--   A buffered forecast-density physical atom is a constant multiple of a normalized polynomial twist
-- statement:
--   **Setup.** Fix the data of OpenAI's allocated layer-sampler setup: a natural number $m$; finite types $G$, $X$, $I_j$, $J_j$ ($j < m$) and $B(a)$ for each layer-sampler axis $a$; dimensions $n_j$; subspaces $U_j \subseteq \mathbb{R}^{J_j}$; bases `basis j` (indexed by $\{0,\dots,n_j-1\}$) of the orthogonal complement of $U_j$; reals $R_j > 0$ and $\sigma_j$; and a `LayerSamplerScale B U basis R σ` $S$. Write `short` = `allocatedShortAxis U basis S.value` and call the other axes active. Let `density` be a real function of pairs (a real vector indexed by $\mathrm{Spatial} = \Sigma_{x \in X} (\mathrm{Unit} \sqcup \emptyset)$, a real vector indexed by the active axes), bounded by $\lvert \mathrm{density}(y)\rvert \le \mathrm{cap}$ and $\mathrm{lip}$-Lipschitz, where $\mathrm{cap}, \mathrm{lip} \in \mathbb{R}_{\ge 0}$. (The hypotheses $hR$, the bound and the Lipschitz property are included in the statement.)
--
--   **Hypotheses.** Let $A$ be a finite type, `Site` a type and $E^{\mathrm{out}}_j$ finite types. Let `selected` $: A \to \Sigma_{j<m}\{0,\dots,n_j-1\}$ with $R_{j_a} \le 1$ for every $a$, where $\texttt{selected}(a) = (j_a, i_a)$. Let $N_{\mathrm{mod}} \ge 1$ and let $\chi$ be an additive character from $(\mathbb{Z}/N_{\mathrm{mod}})^{\mathrm{Out}}$ to $\mathbb{C}$, where $\mathrm{Out}$ = $\Sigma$ `AllocatedCongruenceRankOutput X Eout short`; let $M \ge 1$ with the order of $\chi$ dividing $M$. Let $e(a)$, for $a \in A$, be a `ScalarSiteExpansion Site` (OpenAI structure) satisfying `(e a).Bounds (Tsite a) (Dsite a) (Csite a) Lsite (Hsite a)` for reals $T_{\mathrm{site}}, D_{\mathrm{site}}, C_{\mathrm{site}}, H_{\mathrm{site}}$ and $L_{\mathrm{site}} \in \mathbb{R}_{\ge 0}$; let $k(a)$ be a term of $e(a)$ whose period `(e a).period (k a)` divides $M$; let `site` $\in$ `Site`. Let $\mathrm{base} : X \to \mathbb{Z}$, $\mathrm{physicalN} : X \to \mathbb{N}$, $\tau > 0$. Let $o_j$ be orthonormal bases (indexed by $I_j$) of $U_j$, $bW_j$ $\mathbb{Z}$-bases (indexed by $E^{\mathrm{out}}_j$) of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`, and $hb$: the $\mathbb{Z}$-span of `basis j` is `projectedIntegerLattice (euclideanSubspace (U j))`. Let $C^{\mathrm{fwd}}_j \in \mathbb{R}_{\ge 0}$ with $\lVert \texttt{normalizedOrthogonalChart}(U_j, \texttt{basis}\ j)(v)\rVert \le C^{\mathrm{fwd}}_j \lVert v\rVert$; $K \in \mathbb{R}_{\ge 0}$ with $R_j^{-1} \le K$; $\mathrm{bufferRadius} \in \mathbb{R}_{\ge 0}$ positive; and reals $C_j \ge 0$ with $\lVert \texttt{normalizedOrthogonalChart}(U_j, \texttt{basis}\ j)^{-1}(v)\rVert \le C_j\lVert v\rVert$ and $C_j(\lvert I_j\rvert + 1)(2\,\mathrm{bufferRadius}\, R_j) \le 1/4$, for all $j$ and $v$.
--
--   **Conclusion.** Put (in $\mathbb{R}_{\ge 0}$) $L_{\mathrm{spatial}} = \max(8/\tau, 1)$, $L_{\mathrm{factor}} = (\mathrm{lip} + \lvert A\rvert L_{\mathrm{site}}) L_{\mathrm{spatial}}$, $L_{\mathrm{coord}} = K\sum_j C^{\mathrm{fwd}}_j \lvert J_j\rvert$, $L_{\mathrm{cut}} = (\lvert\text{axes}\rvert\cdot\texttt{normalizedSiteCutoffBound}/(2\,\mathrm{bufferRadius})) L_{\mathrm{coord}}$, $L_g = \max\bigl(L_{\mathrm{factor}} \max(1, L_{\mathrm{coord}}) \max(1, M),\ 4M\bigr)$ and $L_{\mathrm{out}} = L_{\mathrm{cut}} M + L_g$. Then there is a `NormalizedPolynomialTwist X (Σ j, J j) M M Lout` called `twist` (an OpenAI structure) with `twist.modulus` $= M$ and `twist.cover` $= M$ such that:
--
--   1. For all families $\mathrm{poly}_j$ of `VectorPolynomial X ℝ (J j → ℝ)` with all coefficients in $U_j$, all $u : X \to \mathbb{Z}$, all $w_j \in \mathbb{R}^{I_j} \times \mathbb{Z}^{n_j}$ and all $\mathrm{deck}_j \in \mathbb{Z}^{E^{\mathrm{out}}_j}$: if for every $j$
--   $$\texttt{normalizedLatticeRepresentative}(U_j, \texttt{basis}\ j, hb_j)(\texttt{orthonormalMixedChart}(o_j, w_j)) + bW_j(\mathrm{deck}_j) = \texttt{physicalEuclideanSitePoint U poly hpoly}(u)_j$$
--   (where $bW_j(\mathrm{deck}_j)$ is the lattice vector with coordinates $\mathrm{deck}_j$), and every coordinate of `normalizedLatticePoint (U j) (basis j) (orthonormalMixedChart (o j) (w j))` has absolute value at most $1/4$, then
--   $$\kappa(u) \cdot \mathrm{density}\Bigl(\bigl(a \mapsto (u(a) - \mathrm{base}(a))/(\tau\, \mathrm{physicalN}(a)/8)\bigr),\ \texttt{forecastNormalizedActiveCoordinates short}(\texttt{allocatedFullMixedSiteValue U basis w})\Bigr) \cdot \overline{\chi(\omega)} \cdot \Sigma = 2(\mathrm{cap} + 1) \cdot \texttt{twist.eval physicalN poly}\ u,$$
--   where $\kappa(u)$ = `allocatedBufferedTorusCutoff U basis o bufferRadius hbuffer` evaluated at the point $a \mapsto (\mathrm{poly}_{a_1}(u))_{a_{2,2}} \bmod 1$, $\omega$ is the residue vector $\texttt{forecastCongruenceOutput short}\ u\ (j \mapsto (w_j)_2 \sqcup \mathrm{deck}_j)$ reduced modulo $N_{\mathrm{mod}}$, and $\Sigma$ = `siteFamilyFactor e k site` evaluated at the residues $a \mapsto (w_{j_a})_2(i_a) \bmod \texttt{(e a).period (k a)}$ and at the reals $a \mapsto (w_{j_a})_2(i_a) / \texttt{basisAxisScale}(\texttt{basis}\ j_a, i_a)$.
--
--   2. For all such $\mathrm{poly}$ and all $u : X \to \mathbb{Z}$, if $\kappa(u) = 0$ then `twist.eval physicalN poly u` $= 0$.
--
--   All named objects are defined by OpenAI.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_forecastDensityBufferedPhysicalAtom_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.exists_forecastDensityBufferedPhysicalAtom` (in `lean/OAI/Combinatorics/Progressions/Sampling/ForecastDensityPhysicalApproximation.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B199`, `OAIE3v2B217` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/ForecastDensityPhysicalApproximation.lean (declaration OAI.Erdos3.VectorPolynomial.exists_forecastDensityBufferedPhysicalAtom)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B199
import Definitions.Def_OAIE3v2B217

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)

variable (density : ((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ) → ℝ)
variable (cap lip : ℝ≥0)
variable (hbound : ∀ y, |density y| ≤ (cap : ℝ)) (hLips : LipschitzWith lip density)

include hR hbound hLips in
theorem exists_forecastDensityBufferedPhysicalAtom_s2
    {A Site : Type*} [Fintype A]
    {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
    (selected : A → Σ j : Fin m, Fin (n j))
    (hR1 : ∀ a, R (selected a).1 ≤ 1)
    {Nmod : ℕ} [NeZero Nmod]
    (χ : AddChar (Sigma (AllocatedCongruenceRankOutput X Eout short) → ZMod Nmod) ℂ)
    (M : ℕ) [NeZero M] (hM : orderOf χ ∣ M)
    (e : A → ScalarSiteExpansion Site)
    {Tsite Dsite Csite Hsite : A → ℝ} {Lsite : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Tsite a) (Dsite a) (Csite a) Lsite (Hsite a))
    (k : ∀ a, (e a).Term) (site : Site)
    (hd : ∀ a, (e a).period (k a) ∣ M)
    (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ) (hτ : 0 < τ)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
      projectedIntegerLattice (euclideanSubspace (U j)))
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤
      Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (bufferRadius : ℝ≥0) (hbuffer : 0 < bufferRadius)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
      Cinv j * ‖v‖)
    (hbudget : ∀ j, Cinv j * (((Fintype.card (I j) : ℝ) + 1) *
      (2 * (bufferRadius : ℝ) * R j)) ≤ 1 / 4) :
    let Lspatial : ℝ≥0 := max ⟨8 / τ, by positivity⟩ 1
    let Lfactor := (lip + Fintype.card A * Lsite) * Lspatial
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Lcut := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound /
      (2 * bufferRadius)) * Lcoord
    let Lg := max ((Lfactor * max 1 Lcoord) * max 1 (M : ℝ≥0)) (4 * M)
    let Lout := Lcut * M + Lg
    ∃ twist : NormalizedPolynomialTwist X (Σ j, J j) M M Lout,
      twist.modulus = M ∧ twist.cover = M ∧
      (∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ)
          (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (deck : ∀ j, Eout j → ℤ),
        (∀ j, normalizedLatticeRepresentative (euclideanSubspace (U j)) (basis j) (hb j)
          (orthonormalMixedChart (o j) (w j)) + ((bW j).equivFun.symm (deck j)).val =
            physicalEuclideanSitePoint U poly hpoly (fun i => (u i : ℝ)) j) →
        (∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (basis j)
          (orthonormalMixedChart (o j) (w j)) i| ≤ 1 / 4) →
        (allocatedBufferedTorusCutoff (R := R) U basis o bufferRadius hbuffer
          (fun a => ((eval (fun i => (u i : ℝ)) (poly a.1)) a.2.2 : UnitAddCircle)) : ℂ) *
          ((density
            ((fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)),
              forecastNormalizedActiveCoordinates short
                (allocatedFullMixedSiteValue (R := R) U basis w)) : ℂ) *
            star (χ (fun output => (forecastCongruenceOutput (R := ℤ) short u
              (fun j => Sum.elim (w j).2 (deck j)) output : ZMod Nmod))) *
            siteFamilyFactor e k site
              (fun a => ((w (selected a).1).2 (selected a).2 : ZMod ((e a).period (k a))))
              (fun a => ((w (selected a).1).2 (selected a).2 : ℝ) /
                basisAxisScale (basis (selected a).1) (selected a).2)) =
          2 * (((cap : ℝ) + 1 : ℝ) : ℂ) * twist.eval physicalN poly u) ∧
      (∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (_hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ),
        allocatedBufferedTorusCutoff (R := R) U basis o bufferRadius hbuffer
          (fun a => ((eval (fun i => (u i : ℝ)) (poly a.1)) a.2.2 : UnitAddCircle)) = 0 →
        twist.eval physicalN poly u = 0) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
