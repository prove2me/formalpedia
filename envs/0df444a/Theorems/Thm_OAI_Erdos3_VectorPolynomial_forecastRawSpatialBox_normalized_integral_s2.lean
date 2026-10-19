-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_forecastRawSpatialBox_normalized_integral_s2
-- name    : OAI.Erdos3.VectorPolynomial.forecastRawSpatialBox_normalized_integral_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:10:30.951373+00:00
-- url     : https://prove2.me/theorems/b75fc87e-e4c5-4e5b-805f-383534a83ba4
-- title:
--   Rewriting a finite sum of raw mixed-source integrals as a normalized integral over real axes, deck residues and integer axes
-- statement:
--   Let $m$ be a natural number. For $j \in \operatorname{Fin} m$ let $I_j$, $E_j$, $J_j$ be finite types and $n_j$ a natural number; let $N$ be a nonzero natural number. For each $j$ let $U_j$ be a real subspace of $J_j \to \mathbb{R}$ and `basis j` a real basis, indexed by $\operatorname{Fin} n_j$, of the orthogonal complement of `euclideanSubspace (U j)` (that subspace in the Euclidean space $\mathbb{R}^{J_j}$; defined by OpenAI). Let $L$ be a natural number and $X$ a finite type.
--
--   Let `RawSource` be `MixedCoveredJetSource I (fun _ => Unit) E n N`: for each $j$ a real array $I_j \to \mathrm{Unit} \to \mathbb{R}$ and an integer array $\operatorname{Fin} n_j \to \mathrm{Unit} \to \mathbb{Z}$, together with deck residues $\prod_j (\mathrm{Unit} \to E_j \to \mathbb{Z}/N)$ (`ForecastSingleDeckResidues E N`). Let `raw` = `mixedCoveredJetRawReference N`, the product of Lebesgue measure on the real arrays, counting measure on the integer arrays, and the uniform probability measure on the deck residues; let `deckLaw` be the uniform probability measure on the deck residues. The real axes are the pairs $(j, i)$ with $i \in I_j$. Among the integer axes $(j, i)$ with $i \in \operatorname{Fin} n_j$, call an axis short if `basisAxisScale (basis j) i` $\le L^{j+1}$ (`AllocatedShortIntegerAxis U basis L`) and active otherwise (`AllocatedActiveIntegerAxis U basis L`), where `basisAxisScale (basis j) i` $= \lceil \lVert \texttt{basis}_j(i) \rVert^{-1} \rceil$.
--
--   Let $R : \operatorname{Fin} m \to \mathbb{R}$ with all $R_j > 0$, let $F : \mathbb{Z}^X \to \texttt{RawSource} \to \mathbb{C}$, and let $s$ be a finite set of points of $\mathbb{Z}^X$ such that $F(u, \cdot)$ is `raw`-integrable for every $u \in s$ and $F(u, z) = 0$ for all $u \notin s$ and all $z$. Then
--   $$\sum_{u \in s} \int F(u, z)\, d\,\texttt{raw}(z) = \Bigl(\prod_{(j, i)} R_j\Bigr) \int \int \sum_{k_s} \sum_{k} F\Bigl(x \mapsto k(\mathrm{inl}\ x),\ \texttt{forecastSingleMixedRawPoint}\bigl((j,i) \mapsto R_j v_{(j,i)},\ \texttt{forecastIntegerAxisMerge U basis L } k_s\ (k \circ \mathrm{inr}),\ \mathrm{deck}\bigr)\Bigr)\, dv\, d\,\texttt{deckLaw}(\mathrm{deck}),$$
--   where the product is over all real axes $(j, i)$; the outer integral is over deck residues with respect to `deckLaw`, the inner integral is over $v$ in $\mathbb{R}^{\text{real axes}}$ with respect to Lebesgue measure; the first (unconditional) sum is over all $k_s : \text{short axes} \to \mathbb{Z}$ and the second over all $k : X \sqcup \text{active axes} \to \mathbb{Z}$; `forecastIntegerAxisMerge U basis L k_s k_a` is the integer vector on all integer axes equal to $k_s$ on short axes and $k_a$ on active axes; and `forecastSingleMixedRawPoint I E n N v k deck` is the raw source whose real arrays are given by $v$, whose integer arrays are given by $k$, and whose deck residues are `deck` (both maps defined by OpenAI). The sums are `tsum`s of complex numbers.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.forecastRawSpatialBox_normalized_integral_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.forecastRawSpatialBox_normalized_integral` (in `lean/OAI/Combinatorics/Progressions/Sampling/ForecastRawSpatialBoxReorder.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B126` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/ForecastRawSpatialBoxReorder.lean (declaration OAI.Erdos3.VectorPolynomial.forecastRawSpatialBox_normalized_integral)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B126

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} (I E : Fin m → Type*) [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (N : ℕ) [NeZero N]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ) (X : Type*) [Fintype X]

local notation "single" => (fun _ : Fin m => Unit)
local notation "RealAxis" => (Σ j, I j)
local notation "Deck" => ForecastSingleDeckResidues E N
local notation "RawSource" => MixedCoveredJetSource I single E n N
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := single) (E := E) (n := n) N
local notation "deckLaw" => mixedCoveredJetDeckReference single E N
local notation "short" => AllocatedShortIntegerAxis U basis L
local notation "active" => AllocatedActiveIntegerAxis U basis L

theorem forecastRawSpatialBox_normalized_integral_s2
    (R : Fin m → ℝ) (hR : ∀ j, 0 < R j)
    (F : (X → ℤ) → RawSource → ℂ) (s : Finset (X → ℤ))
    (hf : ∀ u ∈ s, Integrable (F u) raw)
    (hzero : ∀ u ∉ s, ∀ z, F u z = 0) :
    (∑ u ∈ s, ∫ z, F u z ∂raw) = ((∏ a : RealAxis, R a.1 : ℝ) : ℂ) *
      ∫ deck : Deck, ∫ v : RealAxis → ℝ,
        ∑' ks : short → ℤ, ∑' k : (X ⊕ active) → ℤ,
          F (fun x => k (Sum.inl x))
            (forecastSingleMixedRawPoint I E n N (fun a => R a.1 * v a)
              (forecastIntegerAxisMerge U basis L ks (fun a => k (Sum.inr a))) deck)
        ∂volume ∂deckLaw := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
