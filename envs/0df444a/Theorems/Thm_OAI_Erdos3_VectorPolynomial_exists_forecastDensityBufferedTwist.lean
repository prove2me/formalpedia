-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_forecastDensityBufferedTwist
-- name    : OAI.Erdos3.VectorPolynomial.exists_forecastDensityBufferedTwist
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T05:34:27.758016+00:00
-- url     : https://prove2.me/theorems/99a12609-3dae-4c39-a067-63859b6308af
-- title:
--   A bounded Lipschitz forecast density factor splits into a mask and a normalized twist
-- statement:
--   Fix the section data: a natural number $m$; finite types $G$ and $X$; finite types $I_j$ and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases `basis j` (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$ for all $j$ (hR); a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities); a function density $: \mathbb R^{\mathrm{Spatial}} \times \mathbb R^{\mathrm{Active}'} \to \mathbb R$, where Spatial $= \Sigma_{x \in X}(\mathrm{Unit} \oplus \mathrm{Empty})$ and $\mathrm{Active}' = \Sigma_{a\ \text{active}}\mathrm{Unit}$, the active axes being those not satisfying short $=$ `allocatedShortAxis U basis S.value`; and $\mathrm{cap}, \mathrm{lip} \in \mathbb R_{\ge 0}$ with $|\mathrm{density}(y)| \le \mathrm{cap}$ for all $y$ (hbound) and density $\mathrm{lip}$-Lipschitz (hLips).
--
--   Let $A$ be a finite type and Site a type; $E^{\mathrm{out}}_j$ finite types; $\mathrm{selected} : A \to \Sigma_j \mathrm{Fin}(n_j)$ with $R_j \le 1$ for $\langle j, i\rangle = \mathrm{selected}(a)$, for all $a$; $N_{\mathrm{mod}} \ne 0$; $\chi$ an additive character of $(\texttt{Sigma (AllocatedCongruenceRankOutput X Eout short)} \to \mathbb Z/N_{\mathrm{mod}})$ with values in $\mathbb C$; $M \ne 0$ with $\mathrm{orderOf}\,\chi \mid M$; a family $e$ of `ScalarSiteExpansion`s on Site indexed by $A$ (each $e_a$ a finite family of terms with periods, complex coefficients and factors $\mathbb Z/p \times \mathbb R \to \mathbb C$) with `(e a).Bounds (Tsite a) (Dsite a) (Csite a) Lsite (Hsite a)` for all $a$, for some reals $T_{\mathrm{site}}, D_{\mathrm{site}}, C_{\mathrm{site}}, H_{\mathrm{site}}$ on $A$ and $L_{\mathrm{site}} \in \mathbb R_{\ge 0}$ (in particular every factor has norm at most $1$ and is $L_{\mathrm{site}}$-Lipschitz in its real argument); a term choice $k_a$ for each $a$ and a site $\mathrm{site}$, with the period of $k_a$ dividing $M$ for all $a$; $\mathrm{base} : X \to \mathbb Z$, $\mathrm{physicalN} : X \to \mathbb N$ and $\tau > 0$; orthonormal bases $o_j$ of `euclideanSubspace (U j)` indexed by $I_j$; $\mathbb Z$-bases $bW_j$ (indexed by $E^{\mathrm{out}}_j$) of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`; $\mathbb Z$-span of `basis j` equal to `projectedIntegerLattice (euclideanSubspace (U j))` (hb); $C_{\mathrm{fwd}} : \mathrm{Fin}\,m \to \mathbb R_{\ge 0}$ with $\|\texttt{normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)}\,v\| \le C_{\mathrm{fwd},j}\|v\|$; $K \in \mathbb R_{\ge 0}$ with $R_j^{-1} \le K$ for all $j$; $\mathrm{coverDegree} \ne 0$ with $M \mid \mathrm{coverDegree}$; $\mathrm{bufferRadius} \in \mathbb R_{> 0}$; and $C_{\mathrm{inv}} : \mathrm{Fin}\,m \to \mathbb R$ with $C_{\mathrm{inv},j} \ge 0$, $\|(\texttt{normalizedOrthogonalChart …})^{-1} v\| \le C_{\mathrm{inv},j}\|v\|$ and $C_{\mathrm{inv},j}(|I_j|+1)\cdot 2\,\mathrm{bufferRadius}\,R_j \le 1/4$ for all $j$. Put $L_{\mathrm{spatial}} = \max(8/\tau, 1)$, $L_{\mathrm{factor}} = (\mathrm{lip} + |A|L_{\mathrm{site}})L_{\mathrm{spatial}}$, $L_{\mathrm{coord}} = K\sum_j C_{\mathrm{fwd},j}|J_j|$, $L_{\mathrm{cut}} = \bigl(|\texttt{LayerSamplerAxis I n}|\cdot\texttt{normalizedSiteCutoffBound}/(2\,\mathrm{bufferRadius})\bigr)L_{\mathrm{coord}}$, $L_g = \max\bigl(L_{\mathrm{factor}}\max(1, L_{\mathrm{coord}})\max(1, M),\ 4M\bigr)$ and $L_{\mathrm{out}} = L_{\mathrm{cut}}M + L_g$.
--
--   Then there exist an additive character mask of $(\mathbb Z/M)^X$ and a function $F$ from residue labels $(\prod_j (\mathrm{Fin}(n_j) \oplus E^{\mathrm{out}}_j \to \mathbb Z/M))$ to functions $\mathbb R^X \times \mathbb R^{\texttt{LayerSamplerAxis I n}} \to \mathbb C$ such that: $|\mathrm{mask}(a)| = 1$ for all $a$; $\|F(a)(v)\| \le 1$ for all $a, v$; each $F(a)$ is $L_{\mathrm{factor}}$-Lipschitz; for all $u : X \to \mathbb Z$, $\mathrm{deck}_j : E^{\mathrm{out}}_j \to \mathbb Z$ and $w$ with $w_j \in \mathbb R^{I_j} \times \mathbb Z^{\mathrm{Fin}(n_j)}$,
--   $$\mathrm{density}\Bigl(\bigl(a \mapsto \tfrac{u_{a} - \mathrm{base}_{a}}{\tau\,\mathrm{physicalN}_{a}/8}\bigr),\ \texttt{forecastNormalizedActiveCoordinates short}\,(\texttt{allocatedFullMixedSiteValue U basis w})\Bigr)\cdot\overline{\chi\bigl(\texttt{forecastCongruenceOutput short u (j ↦ Sum.elim (w j).2 (deck j))} \bmod N_{\mathrm{mod}}\bigr)}\cdot\texttt{siteFamilyFactor e k site}\,\bigl(a \mapsto (w_j)_2(i) \bmod p_{k_a}\bigr)\,\bigl(a \mapsto (w_j)_2(i)/\texttt{basisAxisScale (basis j) i}\bigr)$$
--   $$= (\mathrm{cap}+1)\cdot\overline{\mathrm{mask}(u \bmod M)}\cdot F\bigl(j \mapsto \texttt{Sum.elim}((w_j)_2 \bmod M, \mathrm{deck}_j \bmod M)\bigr)\bigl(u/\mathrm{physicalN},\ \texttt{allocatedFullMixedSiteValue U basis w}\bigr),$$
--   with $\langle j, i\rangle = \mathrm{selected}(a)$ and $a$ in Spatial read through its $X$-component (`allocatedFullMixedSiteValue` sends $\langle j,\mathrm{inl}\,i\rangle \mapsto (w_j)_1(i)/R_j$ and $\langle j, \mathrm{inr}\,i\rangle \mapsto (w_j)_2(i)/\texttt{basisAxisScale}/R_j$); and there exists a `NormalizedPolynomialTwist X (Σ j, J j) M M Lout` twist (a structure bundling a modulus, a cover, a mask on $(\mathbb Z/\mathrm{modulus})^X$ and an $L_{\mathrm{out}}$-Lipschitz smooth part, both of norm at most $1$) with modulus $M$ and cover $M$ such that for all families of `VectorPolynomial X ℝ (J j → ℝ)` $\mathrm{poly}_j$ whose coefficients lie in $U_j$ and all $u : X \to \mathbb Z$,
--   $$(\mathrm{cap}+1)\,\overline{\mathrm{mask}(u \bmod M)}\cdot\texttt{forecastBufferedCoveredSiteFactor B U basis S o hb bW coverDegree bufferRadius hbuffer M F}\,(u/\mathrm{physicalN})\,(\texttt{physicalSingleSiteValue U coverDegree poly hpoly u}) = 2(\mathrm{cap}+1)\cdot\texttt{twist.eval physicalN poly u}.$$
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_forecastDensityBufferedTwist` in `lean/OAI/Combinatorics/Progressions/Sampling/ForecastDensityPhysicalApproximation.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B055`, `OAIErdos3B151`, `OAIErdos3B152` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/ForecastDensityPhysicalApproximation.lean#L148

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B055
import Definitions.Def_OAIErdos3B151
import Definitions.Def_OAIErdos3B152

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

include hR hbound hLips in
theorem exists_forecastDensityBufferedTwist
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
    (coverDegree : ℕ) [NeZero coverDegree] (hcover : M ∣ coverDegree)
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
    ∃ mask : AddChar (X → ZMod M) ℂ,
      ∃ F : (∀ j, Fin (n j) ⊕ Eout j → ZMod M) →
        (X → ℝ) × (LayerSamplerAxis I n → ℝ) → ℂ,
      (∀ a, ‖mask a‖ = 1) ∧ (∀ a v, ‖F a v‖ ≤ 1) ∧
      (∀ a, LipschitzWith Lfactor (F a)) ∧
      (∀ (u : X → ℤ) (deck : ∀ j, Eout j → ℤ)
          (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)),
        (density
          ((fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)),
            forecastNormalizedActiveCoordinates short
              (allocatedFullMixedSiteValue (R := R) U basis w)) : ℂ) *
          star (χ (fun output => (forecastCongruenceOutput (R := ℤ) short u
            (fun j => Sum.elim (w j).2 (deck j)) output : ZMod Nmod))) *
          siteFamilyFactor e k site
            (fun a => ((w (selected a).1).2 (selected a).2 : ZMod ((e a).period (k a))))
            (fun a => ((w (selected a).1).2 (selected a).2 : ℝ) /
              basisAxisScale (basis (selected a).1) (selected a).2) =
        (((cap : ℝ) + 1 : ℝ) : ℂ) * star (mask (fun i => (u i : ZMod M))) *
          F (fun j => Sum.elim (fun i => ((w j).2 i : ZMod M))
            (fun i => (deck j i : ZMod M)))
            (fun i => (u i : ℝ) / physicalN i, allocatedFullMixedSiteValue (R := R) U basis w)) ∧
      ∃ twist : NormalizedPolynomialTwist X (Σ j, J j) M M Lout,
        twist.modulus = M ∧ twist.cover = M ∧
        ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ),
          (((cap : ℝ) + 1 : ℝ) : ℂ) * star (mask (fun i => (u i : ZMod M))) *
            forecastBufferedCoveredSiteFactor B U basis S o hb bW
              coverDegree bufferRadius hbuffer M F (fun i => (u i : ℝ) / physicalN i)
              (physicalSingleSiteValue U coverDegree poly hpoly (fun i => (u i : ℝ))) =
          2 * (((cap : ℝ) + 1 : ℝ) : ℂ) * twist.eval physicalN poly u := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
