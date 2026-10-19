-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_forecastInactive_sliced_fixed_residue_identity_s2
-- name    : OAI.Erdos3.VectorPolynomial.forecastInactive_sliced_fixed_residue_identity_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:30:29.400724+00:00
-- url     : https://prove2.me/theorems/ffe6af7f-6017-46bb-9ebd-5e80d3f3f553
-- title:
--   Residue decomposition of the forecast inactive fixed-output event under the contained progression law
-- statement:
--   Let $m$ be a natural number and $G$ a finite type. For $j \in \operatorname{Fin} m$ let $I_j$ (with decidable equality) and $J_j$ be finite types and $n_j$ a natural number; let $B$ assign a finite type with decidable equality to each element of `LayerSamplerAxis I n` (pairs $(j, a)$ with $a \in I_j \sqcup \operatorname{Fin} n_j$). For each $j$ let $U_j$ be a real subspace of $J_j \to \mathbb{R}$ and $b_j$ a real basis, indexed by $\operatorname{Fin} n_j$, of the orthogonal complement of `euclideanSubspace (U j)` (that subspace in the Euclidean space $\mathbb{R}^{J_j}$; defined by OpenAI). Let $R, \sigma : \operatorname{Fin} m \to \mathbb{R}$ with $R_j > 0$ and $\sigma_j > 0$ for all $j$, and let $S$ be a `LayerSamplerScale B U b R σ` (OpenAI's structure containing a positive natural number `S.value`). Let $A$ be a finite type. In this statement the cube alphabet is the empty type, so each principal integer tuple assigns to each principal index $t$ (an element of `PrincipalTupleIndex B (layerSamplerDegree I n)`) a single integer (indexed by $\mathrm{Option}\ \mathrm{Empty}$, which has one element).
--
--   Let `selected` $: A \to \Sigma_j \operatorname{Fin} n_j$ be injective; let $q$ be a nonzero natural number; let $H, \mathrm{step} : \texttt{PrincipalTupleIndex B (layerSamplerDegree I n)} \to \mathbb{N}$ and `lower` with values in $\mathbb{Z}$ be such that $H(t) > 0$ and (hsubset) the progression `integerProgressionSupport (lower t) (step t) (H t)` (the integers $\mathrm{lower}(t) + \mathrm{step}(t)\, k$, $0 \le k < H(t)$) is contained in $[0, \texttt{allocatedPrincipalSides B U b S t})$ for all $t$. Let `coefficient` be a complex-valued function of residue assignments $t \mapsto (\mathrm{Option}\ \mathrm{Empty} \to \mathbb{Z}/q)$. Assume (hsmall) for each $a \in A$, writing `selected a` $= (j_a, i_a)$, `basisAxisScale (b j_a) i_a` $\le \texttt{S.value}^{j_a + 1}$. Let $c_a$, for $a \in A$, be integer functions on `BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j_a + 1)` with each $c_a(d)$ in the support of the probability mass function `allocatedLayerIntegerPMFs B U b hR hσ S j_a i_a d` (OpenAI's layer integer laws). Let $x : G \to$ `IntegerScalarCubeBox Empty S.value` and $z : A \to \mathbb{Z}$.
--
--   Let $p$ = `principalTupleWeights B (layerSamplerDegree I n) H hH` (the product of uniform laws on the cubes of sizes $H(t)$), let `map` = `containedProgressionTupleMap … H step lower … hsubset` (OpenAI's map embedding each cube coordinate into the progression with start `lower` and step `step`), and let $p.\texttt{fiberLaw map}$ be the image law. For a principal tuple $y$, let `principalResidueLabel q y` be its coordinatewise reduction modulo $q$, and let `forecastInactiveFixedOutput B U b S selected c x y` be OpenAI's map $A \to (\{\varnothing\} \to \mathbb{Z})$ sending $a$ to the product of the bounded coefficient jet matrix of the physical cube determined by $x$ and $y$ (in degree $j_a + 1$) with the vector $c_a$. Then
--   $$\mathbb{E}_{y \sim p.\texttt{fiberLaw map}} \Bigl[ \texttt{coefficient}(\texttt{principalResidueLabel } q\ y) \cdot \mathbf{1}\bigl[\texttt{forecastInactiveFixedOutput}(\dots, y) = (a, \_) \mapsto z(a)\bigr] \Bigr]$$
--   equals
--   $$\sum_{r} p\bigl(\{y : \texttt{principalResidueLabel } q\ y = r\}\bigr) \cdot \texttt{coefficient}\bigl(\texttt{progressionPrincipalResidue step lower q } r\bigr) \cdot \prod\nolimits^{\mathrm{PMF}}_{a \in A} \Pi_{a, r}\bigl((\_ \mapsto z(a))\bigr),$$
--   where the sum runs over residue assignments $r$ whose cell has positive $p$-mass; `progressionPrincipalResidue step lower q r` is the residue assignment $t \mapsto \mathrm{lower}(t) + \mathrm{step}(t) \cdot r(t) \pmod q$ (on the single coordinate `none`); and the last factor is the value at the point $(a, \_) \mapsto z(a)$ of the product probability mass function (`dependentProductPMF`) of the laws $\Pi_{a, r}$ = `allocatedSupportedSlicedResidueJetPMF B U b hR hσ S q r H step lower hH hsubset _ j_a i_a univ (fun _ => c a 0)`, OpenAI's residue-conditioned sliced jet law for the axis $(j_a, i_a)$ on the single row $\varnothing$, shifted by the constant coefficient $c_a(0)$ (with $0$ the constant exponent `constantCoefficientSlot`), cast to a complex number.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.forecastInactive_sliced_fixed_residue_identity_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.forecastInactive_sliced_fixed_residue_identity` (in `lean/OAI/Combinatorics/Progressions/Lattices/ForecastInactiveAffineIntervalFixedResidueSite.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B180`, `OAIE3v2B196`, `OAIE3v2B197` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/ForecastInactiveAffineIntervalFixedResidueSite.lean (declaration OAI.Erdos3.VectorPolynomial.forecastInactive_sliced_fixed_residue_identity)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B180
import Definitions.Def_OAIE3v2B196
import Definitions.Def_OAIE3v2B197

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*} [Fintype A]

attribute [local instance] ScalarSiteExpansion.termFinite

theorem forecastInactive_sliced_fixed_residue_identity_s2
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    (q : ℕ) [NeZero q]
    (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
    (lower : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
    (hH : ∀ t, 0 < H t)
    (hsubset : ∀ t, integerProgressionSupport (lower t) (step t : ℤ) (H t) ⊆
      Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S t : ℤ))
    (coefficient : (PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q) → ℂ)
    (hsmall : ∀ a, basisAxisScale (b (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U b hR hσ S
      (selected a).1 (selected a).2 d).support)
    (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ) :
    let p := principalTupleWeights (α := Empty) B (layerSamplerDegree I n) H hH
    let map := containedProgressionTupleMap B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) H step lower (allocatedPrincipalSides_pos B U b S) hsubset
    (p.fiberLaw map).complexMean (fun y => coefficient (principalResidueLabel q y) *
      (if forecastInactiveFixedOutput B U b S selected c x y = (fun a _ => z a) then 1 else 0)) =
      ∑ r : {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q //
          0 < p.mass (Finset.univ.filter (fun y => principalResidueLabel q y = r))},
        (p.mass (Finset.univ.filter (fun y => principalResidueLabel q y = r.val)) : ℂ) *
          coefficient (progressionPrincipalResidue B (layerSamplerDegree I n) step lower q r.val) *
          ((dependentProductPMF (fun a => allocatedSupportedSlicedResidueJetPMF B U b hR hσ S q r.val
            H step lower hH hsubset r.property (selected a).1 (selected a).2
            (Finset.univ : Finset (Finset Empty)) (fun _ => c a (constantCoefficientSlot _ _)))
            (fun a _ => z a)).toReal : ℂ) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
