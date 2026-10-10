-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_forecastDensityBufferedNativeExpansion
-- name    : OAI.Erdos3.VectorPolynomial.exists_forecastDensityBufferedNativeExpansion
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T05:50:04.67537+00:00
-- url     : https://prove2.me/theorems/268b6eec-3952-4f3e-905c-574016e17d3f
-- title:
--   A combination of normalized forecast atoms is approximated by normalized twists
-- statement:
--   Fix the section data: a natural number $m$; finite types $G$ and $X$; finite types $I_j$ and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases `basis j` (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$ for all $j$ (hR); a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities); a function density $: \mathbb R^{\mathrm{Spatial}} \times \mathbb R^{\mathrm{Active}'} \to \mathbb R$, where Spatial $= \Sigma_{x \in X}(\mathrm{Unit} \oplus \mathrm{Empty})$ and $\mathrm{Active}' = \Sigma_{a\ \text{active}}\mathrm{Unit}$, the active axes being those not satisfying short $=$ `allocatedShortAxis U basis S.value`; and $\mathrm{cap}, \mathrm{lip} \in \mathbb R_{\ge 0}$ with $|\mathrm{density}(y)| \le \mathrm{cap}$ for all $y$ (hbound) and density $\mathrm{lip}$-Lipschitz (hLips).
--
--   Let $A$ and Term be finite types and Site a type; $E^{\mathrm{out}}_j$ finite types; $\mathrm{selected} : A \to \Sigma_j \mathrm{Fin}(n_j)$ with $R_j \le 1$ for $\langle j, i\rangle = \mathrm{selected}(a)$, for all $a$; $N_{\mathrm{mod}} \ne 0$; for each $t \in \mathrm{Term}$ an additive character $\chi_t$ of $(\texttt{Sigma (AllocatedCongruenceRankOutput X Eout short)} \to \mathbb Z/N_{\mathrm{mod}})$ with values in $\mathbb C$; for each $t$ a family $e_t$ of `ScalarSiteExpansion`s on Site indexed by $A$ with `(e t a).Bounds (Tsite t a) (Dsite t a) (Csite t a) Lsite (Hsite t a)` for all $t, a$, for some reals $T_{\mathrm{site}}, D_{\mathrm{site}}, C_{\mathrm{site}}, H_{\mathrm{site}}$ and $L_{\mathrm{site}} \in \mathbb R_{\ge 0}$; a term choice $k_{t,a}$ of $e_{t,a}$ for all $t, a$ and a site $\mathrm{site}$; $\mathrm{base} : X \to \mathbb Z$, $\mathrm{physicalN} : X \to \mathbb N$ and $\tau > 0$; orthonormal bases $o_j$ of `euclideanSubspace (U j)` indexed by $I_j$; $\mathbb Z$-bases $bW_j$ (indexed by $E^{\mathrm{out}}_j$) of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`; $\mathbb Z$-span of `basis j` equal to `projectedIntegerLattice (euclideanSubspace (U j))` (hb); $C_{\mathrm{fwd}} : \mathrm{Fin}\,m \to \mathbb R_{\ge 0}$ with $\|\texttt{normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)}\,v\| \le C_{\mathrm{fwd},j}\|v\|$; $K \in \mathbb R_{\ge 0}$ with $R_j^{-1} \le K$; $\mathrm{bufferRadius} \in \mathbb R_{>0}$; and $C_{\mathrm{inv}} : \mathrm{Fin}\,m \to \mathbb R$ with $C_{\mathrm{inv},j} \ge 0$, $\|(\texttt{normalizedOrthogonalChart …})^{-1}v\| \le C_{\mathrm{inv},j}\|v\|$ and $C_{\mathrm{inv},j}(|I_j|+1)\cdot 2\,\mathrm{bufferRadius}\,R_j \le 1/4$ for all $j$. Put $L_{\mathrm{spatial}} = \max(8/\tau, 1)$, $L_{\mathrm{factor}} = (\mathrm{lip} + |A|L_{\mathrm{site}})L_{\mathrm{spatial}}$, $L_{\mathrm{coord}} = K\sum_j C_{\mathrm{fwd},j}|J_j|$, $L_{\mathrm{cut}} = \bigl(|\texttt{LayerSamplerAxis I n}|\cdot\texttt{normalizedSiteCutoffBound}/(2\,\mathrm{bufferRadius})\bigr)L_{\mathrm{coord}}$, and $\mathrm{period}(t) = \mathrm{orderOf}(\chi_t)\cdot$`commonSitePeriod (e t) (k t)`.
--
--   Then for every real $P \ge 0$ with $\mathrm{period}(t) \le e^P$ for all $t$ and $L_{\mathrm{factor}}, L_{\mathrm{coord}}, L_{\mathrm{cut}} \le e^P$, there exist `NormalizedPolynomialTwist X (Σ j, J j)` structures $\mathrm{twists}_t$ (each bundling a modulus, a cover, a mask and a Lipschitz smooth part of norm at most $1$), with period cap, cover cap and Lipschitz constant all equal to $e^{3P+3}$, such that $\mathrm{twists}_t$ has modulus and cover equal to $\mathrm{period}(t)$ for all $t$, and the following holds. Let $\mathrm{poly}_j$ be `VectorPolynomial X ℝ (J j → ℝ)`s with all coefficients in $U_j$, $\mathrm{coefficient} : \mathrm{Term} \to \mathbb C$, $\mathrm{target} : (X \to \mathbb Z) \to \mathbb C$, and reals mass and $\varepsilon$ with $\sum_t \|\mathrm{coefficient}_t\| \le \mathrm{mass}$ and $\varepsilon \ge 0$. Assume that `allocatedBufferedTorusCutoff U basis o bufferRadius hbuffer` equals $1$ at the torus point $\langle j, \cdot, x\rangle \mapsto \mathrm{poly}_j(u)_x \bmod 1$ whenever $\mathrm{target}(u) \ne 0$; and assume that for all $u : X \to \mathbb Z$, $w$ with $w_j \in \mathbb R^{I_j}\times\mathbb Z^{\mathrm{Fin}(n_j)}$, and $\mathrm{deck}_j : E^{\mathrm{out}}_j \to \mathbb Z$ such that, for every $j$, `normalizedLatticeRepresentative (euclideanSubspace (U j)) (basis j) (hb j) (orthonormalMixedChart (o j) (w j))` plus the lattice vector with $bW_j$-coordinates $\mathrm{deck}_j$ equals `physicalEuclideanSitePoint U poly hpoly u j`, and every coordinate of `normalizedLatticePoint (euclideanSubspace (U j)) (basis j) (orthonormalMixedChart (o j) (w j))` has absolute value at most $1/4$, we have
--   $$\Bigl\|\mathrm{target}(u) - \sum_t \mathrm{coefficient}_t\cdot\texttt{forecastDensityNormalizedAtom B U basis S density cap selected}\ (\chi_t)\ (e_t)\ (k_t)\ \mathrm{site}\ \mathrm{base}\ \mathrm{physicalN}\ \tau\ u\ \mathrm{deck}\ w\Bigr\| \le \varepsilon$$
--   (the atom is the density at the normalized spatial and active coordinates, times $\overline{\chi_t}$ of the congruence output, times the site family factor, divided by $\mathrm{cap}+1$). Then $\sum_t \|2\,\mathrm{coefficient}_t\| \le 2\,\mathrm{mass}$, and for all $u : X \to \mathbb Z$,
--   $$\Bigl\|\mathrm{target}(u) - \sum_t 2\,\mathrm{coefficient}_t\cdot\texttt{(twists t).eval physicalN poly u}\Bigr\| \le \varepsilon.$$
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_forecastDensityBufferedNativeExpansion` in `lean/OAI/Combinatorics/Progressions/Sampling/ForecastDensityPhysicalApproximation.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B178` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/ForecastDensityPhysicalApproximation.lean#L455

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B178

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

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

end Erdos3.VectorPolynomial

end

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

end Erdos3.VectorPolynomial

end

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
theorem exists_forecastDensityBufferedNativeExpansion
    {A Site Term : Type*} [Fintype A] [Fintype Term]
    {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
    (selected : A → Σ j : Fin m, Fin (n j))
    (hR1 : ∀ a, R (selected a).1 ≤ 1)
    {Nmod : ℕ} [NeZero Nmod]
    (χ : Term → AddChar (Sigma (AllocatedCongruenceRankOutput X Eout short) → ZMod Nmod) ℂ)
    (e : Term → A → ScalarSiteExpansion Site)
    {Tsite Dsite Csite Hsite : Term → A → ℝ} {Lsite : ℝ≥0}
    (he : ∀ t a, (e t a).Bounds (Tsite t a) (Dsite t a) (Csite t a) Lsite (Hsite t a))
    (k : ∀ t a, (e t a).Term) (site : Site)
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
    let period := fun t => orderOf (χ t) * commonSitePeriod (e t) (k t)
    ∀ {P : ℝ}, 0 ≤ P →
      (∀ t, (period t : ℝ) ≤ Real.exp P) →
      (Lfactor : ℝ) ≤ Real.exp P → (Lcoord : ℝ) ≤ Real.exp P →
      (Lcut : ℝ) ≤ Real.exp P →
    ∃ twists : Term → NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp (3 * P + 3)) (Real.exp (3 * P + 3))
        ⟨Real.exp (3 * P + 3), Real.exp_nonneg _⟩,
      (∀ t, (twists t).modulus = period t ∧ (twists t).cover = period t) ∧
      ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
        (hpoly : ∀ j v, coefficients (poly j) v ∈ U j)
        (coefficient : Term → ℂ) (target : (X → ℤ) → ℂ) (mass ε : ℝ),
        (∑ t, ‖coefficient t‖) ≤ mass → 0 ≤ ε →
        (∀ u, target u ≠ 0 → allocatedBufferedTorusCutoff (R := R) U basis o
          bufferRadius hbuffer
          (fun a => ((eval (fun i => (u i : ℝ)) (poly a.1)) a.2.2 : UnitAddCircle)) = 1) →
        (∀ (u : X → ℤ) (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ))
          (deck : ∀ j, Eout j → ℤ),
          (∀ j, normalizedLatticeRepresentative (euclideanSubspace (U j)) (basis j) (hb j)
            (orthonormalMixedChart (o j) (w j)) + ((bW j).equivFun.symm (deck j)).val =
              physicalEuclideanSitePoint U poly hpoly (fun i => (u i : ℝ)) j) →
          (∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (basis j)
            (orthonormalMixedChart (o j) (w j)) i| ≤ 1 / 4) →
          ‖target u - ∑ t, coefficient t *
            forecastDensityNormalizedAtom B U basis S density cap selected (χ t) (e t) (k t) site
              base physicalN τ u deck w‖ ≤ ε) →
        (∑ t, ‖(2 : ℂ) * coefficient t‖) ≤ 2 * mass ∧
        ∀ u, ‖target u - ∑ t, ((2 : ℂ) * coefficient t) *
          (twists t).eval physicalN poly u‖ ≤ ε := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
